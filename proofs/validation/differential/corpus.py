"""Load Calibrator definitions as Python callables.

PRIMARY SOURCE is `proofs/validation/extract/api.py`, the project's definition
table.  `leanexpr.py` in this directory is a second, independently written
translator; it is retained for two reasons and only two:

  1. it supplies the ℕ-recursions that `api.callable_for` does not yet emit
     (hetRecurrence, hetMutationDriftRecurrence, driftLDTrajectory, ...);
  2. it is the cross-check.  `crossvalidate.py` runs both over every argument
     tuple the battery evaluates; that comparison is what surfaced the
     `hetDecayFactor` overload mis-resolution.

Where the two disagree, NEITHER is used silently.  The definition goes on the
QUARANTINE list with its evidence, so a translation dispute can never be
mistaken for a finding about population genetics.
"""

from __future__ import annotations

import os
import sys

import leanexpr as L

HERE = os.path.dirname(os.path.abspath(__file__))
CALIBRATOR = os.path.join(os.path.dirname(os.path.dirname(HERE)), "Calibrator")
EXTRACT = os.path.join(os.path.dirname(HERE), "extract")

if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402

MODULES = [
    "PopulationGeneticsFoundations",
    "LDDecayTheory",
    "DemographicHistory",
    "PortabilityDrift",
    "CovarianceStructure",
    "HumanDemography",
]

# Definitions where extract's callable is known-wrong and leanexpr's is used
# instead.  Each entry must carry its evidence; an unexplained override is
# indistinguishable from a thumb on the scale.
QUARANTINE: dict[str, str] = {}

# Resolved, kept as the record of what the mechanism is for:
#   fstMutationDriftTransientDiscrete -- extract bound the unqualified
#   `hetDecayFactor Ne θ` call to a 1-ary structure overload
#   (Calibrator.GenerationalPopGenParameters.hetDecayFactor, DGP's
#   PGSEvolutionaryModel.hetDecayFactor) and raised TypeError. Lean resolves it
#   to Calibrator.hetDecayFactor (PopulationGeneticsFoundations.lean:1341,
#   binders (Ne θ : ℝ)) -- same file, same namespace, matching arity. Found by
#   the leanexpr/extract cross-check, reported, and fixed upstream; the two
#   translators now agree to 10 significant figures. 22 short names in the
#   corpus map to more than one fully-qualified name, so this class of error
#   can recur -- the cross-check stays.


# Short names that collide across the corpus. extract deliberately refuses to
# give these a bare alias -- 22 short names map to more than one FQ name, and
# letting the first emitted definition claim the bare name is what produced the
# `hetDecayFactor` mis-binding. Any such name a check uses must be pinned here,
# explicitly, to the definition the CALLER's file resolves to in Lean.
FQ_OVERRIDES = {
    # PopulationGeneticsFoundations.lean:1341, binders (Ne θ : ℝ). The sibling
    # structure methods (DGP's PGSEvolutionaryModel, PortabilityDrift's
    # GenerationalPopGenParameters) carry the same formula on a record.
    "hetDecayFactor": "Calibrator.hetDecayFactor",
}


def _leanexpr_table():
    table: dict[str, callable] = {}
    defs: dict[str, L.LeanDef] = {}
    for mod in MODULES:
        path = os.path.join(CALIBRATOR, mod + ".lean")
        if not os.path.exists(path):
            continue
        for d in L.extract_file(path, mod) + L.extract_recursions(path, mod):
            if d.name in defs:
                continue
            defs[d.name] = d
            if d.py_src is None:
                continue
            try:
                table[d.name] = (
                    L.compile_recursion if d.is_recursion else L.compile_def
                )(d, table)
            except L.Unsupported:
                pass
    return table, defs


def load():
    """Return (callables, provenance, unavailable).

    `callables` is keyed by BARE Lean name for use inside checks; `provenance`
    records the fully-qualified name, source, checksum and which translator
    produced each one.  Results are reported under the FQ name.

    The corpus is namespace-flat: the fully-qualified name of `coalFst` is
    `Calibrator.coalFst`, NOT `Calibrator.PopulationGeneticsFoundations.coalFst`
    -- every file opens `namespace Calibrator` and the module path is not part
    of the name.
    """
    mine, mine_defs = _leanexpr_table()
    table: dict[str, callable] = {}
    prov: dict[str, dict] = {}
    unavailable: dict[str, str] = {}

    names = set(mine) | {fq.split(".")[-1] for fq in api.definition_table()}

    for name in sorted(names):
        if name in FQ_OVERRIDES:
            fq, fq_err = FQ_OVERRIDES[name], None
        else:
            try:
                fq, fq_err = api.resolve(name), None
            except Exception as e:
                fq, fq_err = None, f"{type(e).__name__}: {e}"

        theirs = None
        if fq is not None:
            try:
                theirs, _ = api.callable_for(fq)
            except Exception as e:
                fq_err = f"{type(e).__name__}: {e}"

        if name in QUARANTINE and name in mine:
            d = mine_defs[name]
            table[name] = mine[name]
            prov[name] = {
                "fq": fq or f"Calibrator.{name}",
                "translator": "leanexpr (extract QUARANTINED)",
                "quarantine_reason": QUARANTINE[name],
                "source": f"{d.module}.lean:{d.line}",
                "leanexpr_sha16": d.sha256,
            }
            continue

        if theirs is not None:
            table[name] = theirs
            d = api.definition(fq)
            prov[name] = {
                "fq": fq,
                "translator": "extract",
                "source": f"{d['file']}:{d['line']}",
                "checksum": api.body_checksum(fq),
                "empirical_status": d.get("empirical_status"),
                "admissible_box": api.admissible_box(fq),
                "also_in_leanexpr": name in mine,
            }
        elif name in mine:
            d = mine_defs[name]
            table[name] = mine[name]
            prov[name] = {
                "fq": fq or f"Calibrator.{name}",
                "translator": "leanexpr (extract unavailable)",
                "extract_error": fq_err,
                "source": f"{d.module}.lean:{d.line}",
                "leanexpr_sha16": d.sha256,
            }
        else:
            unavailable[name] = fq_err or "not extractable by either translator"

    return table, prov, unavailable
