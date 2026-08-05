"""Regenerate fixtures.json and expected.json.

`fixtures.json` is the expensive artifact: the boundary and degenerate input
list, chosen so that a wrong body has somewhere to show itself.  It is committed
rather than generated at check time so that the check is a comparison against a
fixed grid and not against whatever the generator happens to emit today.

`expected.json` holds the Lean-side answers on that grid.  `map_check.py`
regenerates it and requires an exact match, so the committed answers cannot
drift away from `lean_bodies.py`; the Rust differential test consumes the same
file, so both sides are compared against one artifact rather than against each
other's convenience.

Run:  python3 gen_fixtures.py
"""

import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import lean_bodies  # noqa: E402


def _class(name, markers, differentiation, rank=1):
    return {"name": name, "effective_independent_markers": markers,
            "differentiation": differentiation, "theoretical_pc_rank": rank}


APPLICATION = {"susceptibility": 1e-5, "expected_pgs_variants": 10000.0,
               "effect_sd": 0.1, "directional_amplification": 2.0,
               "count_inflation": 0.0, "confounder": 0.5, "critical_signal": 3.85}


def designs():
    out = []

    def design(tag, n, m, fitted, classes, app=None):
        record = {"tag": tag, "sample_size": n, "subgroup_size": m,
                  "fitted_pcs": fitted, "marker_classes": classes}
        if app is not None:
            record["application"] = app
        out.append(record)

    # The three fixtures the shipped module tests itself on, verbatim.  If the
    # implementation's own unit tests and this grid ever disagree about the same
    # inputs, one of the two is lying about what the calculator does.
    design("shipped-unit-1", 400000.0, 1000.0, 40,
           [_class("common", 100000.0, 0.0001), _class("rare", 1000000.0, 0.001)])
    design("shipped-unit-2", 100000.0, 1000.0, 40,
           [_class("common", 100000.0, 0.0001)], APPLICATION)
    # The pair that separates the fitted-PC gate from the spectral gate: same
    # design, detectable axis at rank 3, fitted_pcs below and then above it.
    design("shipped-unit-3-rank-outside-budget", 1000.0, 500.0, 2,
           [_class("channel", 4000.0, 0.01, 3)])
    design("shipped-unit-3-rank-inside-budget", 1000.0, 500.0, 3,
           [_class("channel", 4000.0, 0.01, 3)])

    # Coarse grid.  Small enough to stay inside the workflow's twenty-second
    # empirical budget, wide enough that the spike spans several decades and the
    # aspect ratio crosses one in both directions.
    index = 0
    for n in (10.0, 1000.0, 1e5, 4e5):
        for fraction in (1e-4, 0.1, 0.5, 0.999):
            for markers in (1.0, 4000.0, 1e6, 1e9):
                for differentiation in (0.0, 1e-9, 1e-4, 0.01, 0.5, 1.0):
                    m = n * fraction
                    if not 0.0 < m < n:
                        continue
                    index += 1
                    design(
                        f"grid-{index}", n, m, 1 + (index % 4),
                        [_class(f"c{index}", markers, differentiation),
                         # a second class keeps at least one positive
                         # differentiation, which the validator requires, and
                         # exercises the cross-class normalisation of
                         # matched_weight
                         _class(f"d{index}", markers * 3, max(differentiation, 1e-6), 2)],
                        APPLICATION if index % 3 == 0 else None)

    # Straddling the BBP edge.  The detectability test compares `spike` with
    # `sqrt(aspect)` while the overlap formula divides by `spike^2`, and those
    # two are not equivalent in binary floating point.  If they ever come apart,
    # a shipped report carries a negative removed_axis_fraction.
    for n, markers, m in ((1000.0, 4000.0, 500.0), (1e5, 1e6, 1000.0)):
        effective = m * (n - m) / n
        edge = math.sqrt(n / markers) / (4 * effective)
        for epsilon in (-1e-9, -1e-15, 0.0, 1e-15, 1e-9):
            design(f"edge-{n:g}-{epsilon:g}", n, m, 3,
                   [_class("edge", markers, edge * (1 + epsilon), 1)], APPLICATION)

    # Application-parameter degeneracies: the sqrt(1 + count_inflation)
    # normaliser, a zero and a negative confounder, an extreme directional
    # ascertainment.
    for count_inflation in (0.0, 1e-12, 1.0, 100.0):
        for directional in (0.0, 2.0, 100.0):
            for confounder in (-1.0, 0.0, 0.5):
                app = dict(APPLICATION, count_inflation=count_inflation,
                           directional_amplification=directional, confounder=confounder)
                design(f"app-{count_inflation:g}-{directional:g}-{confounder:g}",
                       1000.0, 500.0, 3, [_class("app", 4000.0, 0.01, 1)], app)

    return out


def main():
    fixtures = designs()
    expected = [lean_bodies.report(design) for design in fixtures]
    # allow_nan=False on purpose. Python would happily write `NaN`/`Infinity`,
    # which is not JSON and which serde_json refuses to parse, so a
    # non-finite Lean-side value would surface as an unreadable fixture file on
    # the Rust side rather than as the finding it is.
    (HERE / "fixtures.json").write_text(
        json.dumps(fixtures, indent=1, sort_keys=True, allow_nan=False) + "\n")
    (HERE / "expected.json").write_text(
        json.dumps(expected, indent=1, sort_keys=True, allow_nan=False) + "\n")
    print(f"fixtures={len(fixtures)} expected={len(expected)}")


if __name__ == "__main__":
    main()
