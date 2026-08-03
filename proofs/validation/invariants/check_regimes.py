#!/usr/bin/env python3
"""Reject external theorem packaging in production Lean structures.

Model data and genuine algebraic laws may live in structures.  A scientific or
analytic conclusion may not be accepted from a caller and then re-exported by
field projection.  This check guards the concrete anti-patterns removed from the
Calibrator corpus and rejects bare ``Prop`` switches, which carry no mathematical
content at all.

Lean compilation remains the proof check.  This file is an architectural check
that prevents the old ``AssumedTheorem.result`` interface from returning under a
new edit.
"""

from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[3]
SOURCE_ROOT = REPO / "proofs" / "Calibrator"

# Names used by the historical result-as-data interfaces.  Exact matching keeps
# legitimate algebraic fields such as ``stationary`` and ``mass_sum`` legal.
FORBIDDEN_FIELDS = {
    "accuracy",
    "barrier",
    "complete",
    "completeness",
    "freezing",
    "identification",
    "limit_adequate",
    "maximalSpectrum",
    "recovered_eq",
    "renormalization",
    "transferThreshold",
}

# WHY THIS LIST EXISTS, AND WHY DELETING AN ENTRY IS NOT A FIX.
#
# Every name here was a structure whose Prop-valued fields CONTAINED THE DESIRED
# CONCLUSION, paired with a theorem that reached that conclusion by `rw` or `exact` on one
# of those fields. `kernelTrivial_of_no_section` applied `D.dichotomy`;
# `assumedCeiling_collapses_to_support_wall` rewrote with `C.characterization`. The
# statement's content was the assumption, so it was not a theorem of this corpus.
#
# Naming such a structure `Assumed...` does not repair it. That is why
# `AssumedDeploymentCeiling` and `AssumedMembraneThreshold` are on this list despite having
# been honestly named: an honest name on a restatement still yields a restatement.
#
# THE ENTRIES ARE NOT STALE CRUFT. A name here means the structure was deleted deliberately
# and must not return. If `check_regimes` fails on one of these, something reintroduced it,
# and the repair is to remove the reintroduction — NOT to prune the list. Pruning restores
# the blindness rather than fixing the break, which is the failure mode every guard in this
# corpus has eventually suffered.
#
# The honest alternative, when the underlying input is real, is the one used in
# `Calibrator.BundleRigidity.DeploymentCeiling`: state the input as a TYPED HYPOTHESIS of
# the theorem that needs it, so it appears in the signature and cannot be forgotten, and
# leave the unproved direction as a named gap with no theorem attached. A used hypothesis
# is an argument of the theorem that needs it; an unused one in a record is decoration.
FORBIDDEN_STRUCTURES = {
    "AtomicCramerFailure",
    "AssumedDeploymentCeiling",
    "AssumedMembraneThreshold",
    "BundleDichotomy",
    "ChaosSpectroscopy",
    "CycleDeterminacy",
    "FittedSelectionLaw",
    "FreezingTransition",
    "GaussianLiabilityRegime",
    "GenotypeChaosLimits",
    "InfiniteIslandLimit",
    "LDBandIntegralIdentification",
    "LinearArchitectureCertificateAssumptions",
    "MarkovModulatedChain",
    "MeanAbsoluteEffectCertificateAssumptions",
    "MellinProfile",
    "MomentReading",
    "ObservableDegradation",
    "ObservableTower",
    "PGSBenDavidCertificate",
    "PowerAgreement",
    "RecoveryAttenuation",
    "ScaleSequence",
    "SubthresholdPCCertificate",
    "TowerRigidity",
    "TransferThreshold",
    "TwoPointIdentification",
    "VertexWeightCompleteness",
}

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
STRUCTURE = re.compile(
    r"^structure\s+([A-Za-z_][A-Za-z0-9_']*)[^\n]*\swhere\n"
    r"((?:(?:[ \t]+[^\n]*)?\n)*)",
    re.M,
)
FIELD = re.compile(r"^[ \t]+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^\n]+)$", re.M)


def main() -> None:
    violations = []
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        text = BLOCK_COMMENT.sub("", path.read_text(encoding="utf-8"))
        for match in STRUCTURE.finditer(text):
            structure = match.group(1)
            rel = path.relative_to(REPO)
            if structure in FORBIDDEN_STRUCTURES:
                violations.append(f"{rel}: forbidden result carrier {structure}")
            for field, type_text in FIELD.findall(match.group(2)):
                if field in FORBIDDEN_FIELDS:
                    violations.append(
                        f"{rel}: {structure}.{field} packages an advertised result"
                    )
                if type_text.strip() == "Prop":
                    violations.append(
                        f"{rel}: {structure}.{field} is a content-free bare Prop switch"
                    )

    if violations:
        print("\n".join(violations))
        raise SystemExit(1)
    print("NO_EXTERNAL_THEOREM_PARAMETERS\tOK")


if __name__ == "__main__":
    main()
