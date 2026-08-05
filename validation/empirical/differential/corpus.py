"""Load Descent definitions as Python callables.

PRIMARY SOURCE is `validation/empirical/extract/api.py`, the project's definition
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
CORPUS = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(HERE))), "Descent")
EXTRACT = os.path.join(os.path.dirname(HERE), "extract")

if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402

# Pin the argument convention rather than discovering a change from a
# TypeError. 1 = scalars only; 2 = sequence-valued (Fin n -> R) arguments also
# supported. A bump means signatures may have changed shape underneath us.
EXPECTED_ARG_CONVENTION = 2
if getattr(api, "ARG_CONVENTION", 1) != EXPECTED_ARG_CONVENTION:
    raise RuntimeError(
        f"extract api.ARG_CONVENTION is {getattr(api, 'ARG_CONVENTION', 1)}, "
        f"this battery was written against {EXPECTED_ARG_CONVENTION}. "
        "Re-check every vector-valued call site before bumping."
    )

def _all_modules():
    """Every Descent .lean file, discovered rather than listed.

    This was a hardcoded list of six files, and that was a latent bug of
    exactly the kind extract's key contract warns about. Commit f959f027
    relocated definitions between files -- fstMutationDriftEquilibrium and
    scaledMutationRate to DGP.lean, cumulativeDrift to DemographicHistory,
    harmonicMeanNe to LDDecayTheory -- with identical bodies. DGP.lean was not
    on the list, so definitions that moved there silently disappeared from the
    leanexpr table and the cross-check count fell from 43 to 37.

    Nothing about a definition's identity is tied to its file: a declaration
    can move between files in the same namespace and keep its fully-qualified
    name. So the file set is discovered, never enumerated. The dependency table
    is global for the same reason -- a callee that moves must still resolve.

    Discovery was still scoped one directory too narrowly: the glob below walks
    CORPUS/**, which does not include `Descent.lean` -- the corpus ROOT,
    a sibling of that directory rather than a child. "Discovered, never enumerated"
    was true and still missed a file, because the discovery root was wrong. A
    dead-code scan with the same blind spot deleted `decaySlope` and then
    `LDDecayMechanism` as unreferenced; their only consumer was a theorem in the root.
    """
    import glob
    out = []
    for path in sorted(glob.glob(os.path.join(CORPUS, "**", "*.lean"),
                                 recursive=True)):
        out.append(os.path.relpath(path, CORPUS)[: -len(".lean")])
    if os.path.exists(_module_path("Descent")):
        out.append("Descent")
    return out


def _module_path(mod):
    """Filesystem path for a module name.

    THE ROOT MODULE IS A SIBLING OF `CORPUS/`, NOT A CHILD. `Descent`
    lives at `Descent.lean`; every other module `Foo` lives at
    `Descent/Foo.lean`. Joining CORPUS with the module name is
    right for all of them except the one that names the directory itself.

    This existed as a half-applied fix: `_all_modules` was corrected to
    DISCOVER the root, and the caller still rebuilt its path as
    `CORPUS/Descent.lean`, so discovery succeeded and the open failed
    with FileNotFoundError. Both halves now go through here, so they cannot
    disagree again -- which is the actual defect, not the missing directory
    level.
    """
    if mod == "Descent":
        return os.path.join(os.path.dirname(CORPUS.rstrip(os.sep)),
                            "Descent.lean")
    return os.path.join(CORPUS, mod + ".lean")

# Definitions where extract's callable is known-wrong and leanexpr's is used
# instead.  Each entry must carry its evidence; an unexplained override is
# indistinguishable from a thumb on the scale.
QUARANTINE: dict[str, str] = {}

# Resolved, kept as the record of what the mechanism is for:
#   fstMutationDriftTransientDiscrete -- extract bound the unqualified
#   `hetDecayFactor Ne θ` call to a 1-ary structure overload
#   (Descent.GenerationalPopGenParameters.hetDecayFactor, DGP's
#   PGSEvolutionaryModel.hetDecayFactor) and raised TypeError. Lean resolves it
#   to Descent.hetDecayFactor (PopulationGeneticsFoundations.lean:1341,
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
    "hetDecayFactor": "Descent.hetDecayFactor",
    # Core/Fst.lean:78, `2 * ploidy * Ne * μ`.  The other bearer of this short
    # name, `Descent.scaledMutationRate` (DGP.lean:52), is a pure delegation TO
    # this one -- so the two are extensionally equal and the ambiguity is not a
    # disagreement about the value, only about which layer owns it.  It is
    # pinned to the KERNEL rather than the shim on purpose: the shim is one of
    # the 171 delegations scheduled for deletion, and a pin to a wrapper would
    # turn that deletion into a battery failure that says nothing about
    # population genetics.
    #
    # Until this entry existed `api.resolve` refused the name as ambiguous,
    # `load()` dropped it from the callable table, and both
    # `hetEquilibrium-vs-exact-iam` and `hetDecayFactor-vs-exact-eigenvalue`
    # raised `KeyError: 'scaledMutationRate'` at every grid point.  The first
    # declares `expected_verdict="AGREE"`, so it reported as a REGRESSION; the
    # second declares none, so it went quiet -- which is exactly the asymmetry
    # the pin on the first was added to expose.
    "scaledMutationRate": "Descent.Core.scaledMutationRate",
    # Same shape: Core/Fst.lean:87 is the kernel, DGP.lean:78 delegates to it.
    # Not currently reached by a check, but it collides identically and pinning
    # it here keeps the two halves of one convention from drifting apart.
    "scaledMigrationRate": "Descent.Core.scaledMigrationRate",
}


def _leanexpr_table():
    table: dict[str, callable] = {}
    defs: dict[str, L.LeanDef] = {}
    for mod in _all_modules():
        path = _module_path(mod)
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
    `Descent.coalFst`, NOT `Descent.PopulationGeneticsFoundations.coalFst`
    -- every file opens `namespace Descent` and the module path is not part
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
                "fq": fq or f"Descent.{name}",
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
                "fq": fq or f"Descent.{name}",
                "translator": "leanexpr (extract unavailable)",
                "extract_error": fq_err,
                "source": f"{d.module}.lean:{d.line}",
                "leanexpr_sha16": d.sha256,
            }
        else:
            unavailable[name] = fq_err or "not extractable by either translator"

    return table, prov, unavailable
