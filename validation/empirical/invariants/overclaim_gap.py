"""Find docstrings that claim more than their theorem proves.

WHY

A Lean theorem cannot be false. Its docstring can, and the docstring is what a
reader takes away. The gap between them is the one defect class the kernel
cannot catch, and it is the same class as proof laundering: the statement is
sound, the claim attached to it is not.

Two shapes are checkable from the sources alone.

EQUIVALENCE CLAIMED, ONE DIRECTION PROVED

A docstring saying "exactly when", "if and only if", "precisely when" or
"necessary and sufficient", attached to a statement with no `↔`.  Sometimes the
converse sits in an adjacent theorem and the package really is an equivalence,
so this reports rather than accuses -- but each entry has to be checked, because
the honest version is cheap:

    constantConditional_driftDefect_zero  said the defect vanishes "exactly
    when" the conditional does not drift, and proved only that a constant
    conditional has zero defect.  The converse needed six lines and a positivity
    hypothesis that turned out to matter: an ancestry of weight zero contributes
    nothing to the defect and its conditional is unconstrained.

ORDER CLAIMED, INSTANCE PROVED

A docstring asserting a general ordering -- "more X means more Y" -- attached to
a closed numeric instance.  The failure mode is real and was found here by
external review: a resolution/defect co-monotonicity claim held along nested
information filtrations and failed for unrelated predictors, with a two-bit
counterexample.  See `MetricSpecificPortability.lean`, where the counterexample
is now formalised beside the nested statement.

WHAT TO DO WITH AN ENTRY

Three honest repairs, in order of preference: prove the converse; weaken the
docstring to what the statement says; or formalise the counterexample that shows
the general reading is false. The third is the most valuable, because it stops
the claim being re-made.

    python3 overclaim_gap.py             # counts and entries
    python3 overclaim_gap.py --file NAME # one module
"""

from __future__ import annotations

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve()
CORPUS = HERE.parents[3] / "Descent"

# The docstring body must not itself contain `-/`.  Without that the non-greedy
# match starts at an EARLIER `/--` -- a definition's docstring, say -- and ends at
# the theorem's own `-/`, swallowing everything between and attributing the
# definition's prose to the theorem.  Six entries were that artefact:
# hweLatticeCondition, IsCompleteCatalogue, lagSensitivityMatrix,
# contextMatchQuality, algorithmicRiskSignature and AlgorithmicallyEquivalent.
PAIR = re.compile(
    r"/--((?:(?!-/)(?:.|\n))*?)-/\s*\n(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+"
    r"([A-Za-z0-9_']+)((?:.|\n)*?):=", re.M)

IFF = re.compile(
    r"if and only if|exactly when|precisely when|necessary and sufficient",
    re.I)

# Entries read and judged benign, with the reason. The phrase is in the
# docstring but is not a claim about THIS theorem's statement: it describes a
# companion result, a hypothesis, or when the lemma has content at all. Kept as
# a list rather than a lexical rule because no rule separated these from the
# real ones -- "zero exactly when the merged ancestries carried the same risk"
# and "has content exactly when the caller supplies a nontrivial transfer" are
# the same shape and only one is a claim.
ACKNOWLEDGED = {
    "sameTransfer_refl": "describes when the lemma has content, not what it proves",
    "rademacher_point_killed": "describes the arithmetic core, not an equivalence",
    "treatNetBenefit_eq": "describes the threshold rule, a companion fact",
    "no_regretFree_action_of_crossing": "names the dichotomy completed by the previous theorem",
    "sixthMoment_eq_floorOne_plus_dispersion": "describes what the panel effect is",
    "hudsonCalibrated_stratification_imitable_if_within_budget": "states the membership criterion it proves",
    "conflict_nonneg": "describes the Cauchy-Schwarz gap, not an iff",
    "portability_gap_decomposition": "points forward to a later section",
    "mul_sq_sub_lt_of_lt_of_ne": "describes what both downstream comparisons reduce to",
    "mul_le_self_of_le_one": "describes the modelling reading",
    "belowThresholdMass_eq_zero": "explicitly a package with aboveThresholdMass_eq_zero",
    "belowThresholdMass_pos_inside": "explicitly a package with the two vanishing results",
    "two_term_weighted_sum_lt_of_larger_weight_gain": "describes when the claim has content",
    "not_isNull_of_demographicSpike_gt_budget": "explicitly a package with the previous theorem",
    "maf_spectrum_identifiable": "describes when the separation hypothesis fails, via a cited theorem",
    "rsquared_eq_process_moments": "describes the guard's behaviour, not the theorem",
    "excess_le_two_mul_perturbation": "compares to the sharp form below",
    "driftLDTrajectory_closedForm": "describes the retention factor, a companion fact",
    "centeredSquare_third_moment_factored": "names the kurtosis phase boundary the factorization exposes",
    "amEquilibriumVariance_at_full_heritability": "describes why a disagreement was invisible",
    "sign_erasure": "converse adjacent",
    "constantConditional_of_driftDefect_zero": "is itself the converse",
    "gaussianKurtosisMaf_lt_quarter": "describes when the fourth-cumulant channel closes, not this bound",
    "rigidity_of_boundedBelowAbove": "the converse is inequivalent_of_unbounded_coding, named in the docstring",
    "qst_no_within": "describes where the map reaches one, which is what this endpoint fixes",
    "realWorldPGSVariance_at_reference_point": "describes when two readings of the variance agree, a companion fact",
    "harmonicMigrationMean_eq_iff_symmetric": "explicitly a package with the inequality above, as the docstring says",
}


def scan() -> list[tuple[str, str, str]]:
    out: list[tuple[str, str, str]] = []
    for f in sorted(CORPUS.rglob("*.lean")):
        txt = f.read_text(encoding="utf-8")
        names = set(re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)",
            txt, re.M))
        for m in PAIR.finditer(txt):
            doc, name, stmt = m.group(1), m.group(2), m.group(3)
            if "↔" in stmt:
                continue
            hit = IFF.search(doc)
            if not hit:
                continue
            # A junk-branch naming states a VALUE at a point.  Its docstring says which
            # point -- "reports no risk exactly when the effect units are degenerate" --
            # and there is no equivalence in it to claim.  The naming convention is the
            # rule, so this needs no per-theorem entry.
            if name.endswith("_is_junk"):
                continue
            # A converse stated nearby, by the corpus's own naming habit.
            stem = name.split("_")[0]
            converse = any(
                other != name and other.startswith(stem)
                and ("_of_" in other or other.endswith("_converse")
                     or "_iff" in other)
                for other in names)
            if converse or name in ACKNOWLEDGED:
                continue
            out.append((name, f.relative_to(CORPUS).as_posix(),
                        hit.group(0).lower()))
    return out


def main(argv: list[str]) -> int:
    if not CORPUS.is_dir():
        print(f"corpus not found at {CORPUS}", file=sys.stderr)
        return 2
    rows = scan()
    print(f"{len(rows)} one-directional theorems whose docstring claims an "
          f"equivalence")

    if "--file" in argv:
        want = argv[argv.index("--file") + 1]
        rows = [r for r in rows if want in r[1]]
        print(f"{len(rows)} of those are in {want}")
    else:
        print()
        by_file = collections.Counter(f for _, f, _ in rows)
        for f, c in by_file.most_common(12):
            print(f"  {c:4d}  {f}")
    print()
    for name, f, note in rows:
        print(f"  {name:54s} {note:38s} {f}")
    print()
    print("Reports, does not accuse: the converse is sometimes an adjacent")
    print("theorem and the package really is an equivalence. Each entry still")
    print("has to be read, because a docstring is what a reader takes away.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
