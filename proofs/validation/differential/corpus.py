"""Load every mechanically-extractable Calibrator definition as a Python callable."""

from __future__ import annotations

import os

import leanexpr as L

CALIBRATOR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "Calibrator",
)

MODULES = [
    "PopulationGeneticsFoundations",
    "LDDecayTheory",
    "DemographicHistory",
    "PortabilityDrift",
    "CovarianceStructure",
    "HumanDemography",
]


def load(modules: list[str] | None = None):
    """Return (callables, defs, failures).

    `callables` maps bare Lean name -> Python function.  Bodies that reference
    other definitions look them up in this same table at call time, so a
    definition whose dependency is not extractable raises KeyError when called
    rather than returning a plausible wrong number.
    """
    mods = modules or MODULES
    table: dict[str, callable] = {}
    defs: dict[str, L.LeanDef] = {}
    failures: dict[str, str] = {}
    for mod in mods:
        path = os.path.join(CALIBRATOR, mod + ".lean")
        if not os.path.exists(path):
            continue
        found = L.extract_file(path, mod) + L.extract_recursions(path, mod)
        for d in found:
            if d.name in defs:
                continue  # first definition wins; duplicates are reported below
            defs[d.name] = d
            if d.py_src is None:
                failures[f"{mod}.{d.name}"] = d.error or "?"
                continue
            try:
                fn = (L.compile_recursion if d.is_recursion else L.compile_def)(d, table)
            except L.Unsupported as e:
                failures[f"{mod}.{d.name}"] = str(e)
                continue
            table[d.name] = fn
    return table, defs, failures
