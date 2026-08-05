"""Hand-translated Lean statements, each traceable to its declaration.

This is the expensive artifact of the SMT lane and the reason this directory
exists: an automatic Lean-to-SMT translator is a research project, so the
statements that matter are transcribed BY HAND, reviewed, and kept here where
they can be re-run and argued with.

Every entry carries `fqn`, the fully-qualified Lean name it transcribes.  It is
anchored to the DECLARATION NAME, never to a line number -- `extract/test_parser.py`
was excluded from CI for pinning line numbers and any edit above a declaration
broke it.  If a declaration is renamed, the entry must be REPOINTED, not left
red: a red ground-truth file stops being read.

TRANSCRIPTION IS THE RISK.  A mistranslated statement produces a confident
finding about nothing.  Two rules keep that honest:

  1. Each entry states its hypotheses and conclusion separately, in the same
     order as the Lean binders, so the transcription can be diffed against the
     source by eye.
  2. `verdict` records what the SMT run is EXPECTED to produce.  An entry that
     stops producing its expected verdict is a regression -- including the
     known-false ones.  A false statement that silently starts verifying means
     somebody weakened it, which is exactly the laundering this corpus forbids.

`z3.Real` names are the Lean binder names wherever Lean's identifier syntax
allows it.
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class Statement:
    key: str
    fqn: str                  # fully-qualified Lean declaration, or "" if planted
    note: str
    hyps: list                # callables: (vars dict) -> z3 BoolRef
    concl: object             # callable: (vars dict) -> z3 BoolRef
    vars: list[str] = field(default_factory=list)
    # SAT-on-negation => a counterexample exists => statement is FALSE
    # UNSAT-on-hypotheses => vacuous
    verdict: str = "HOLDS"    # HOLDS | FALSE | VACUOUS
    witness: dict | None = None   # the counterexample, when verdict == FALSE


STATEMENTS: list[Statement] = []


def stmt(**kw):
    STATEMENTS.append(Statement(**kw))


# ===========================================================================
# 1. CALIBRATION STATEMENTS -- planted, not from the corpus.
#
# These are the permanent both-directions calibration for the SMT encoding.
# Three that are true, three that are false, one vacuous.  A regression in the
# encoding, the solver version, or the arithmetic setup shows up here first.
# ===========================================================================

stmt(key="calib-amgm", fqn="", verdict="HOLDS",
     note="AM-GM squared: 0<a, 0<b -> 4ab <= (a+b)^2.",
     vars=["a", "b"],
     hyps=[lambda v: v["a"] > 0, lambda v: v["b"] > 0],
     concl=lambda v: 4 * v["a"] * v["b"] <= (v["a"] + v["b"]) ** 2)

stmt(key="calib-cauchy-schwarz", fqn="", verdict="HOLDS",
     note="Cauchy-Schwarz in the plane; no hypotheses at all.",
     vars=["a", "b", "c", "d"],
     hyps=[],
     concl=lambda v: (v["a"] * v["c"] + v["b"] * v["d"]) ** 2
     <= (v["a"] ** 2 + v["b"] ** 2) * (v["c"] ** 2 + v["d"] ** 2))

stmt(key="calib-portability-shape", fqn="", verdict="HOLDS",
     note="The shape most corpus bounds take: 0<=r<=1, 0<=f<=1 -> r(1-f) <= r.",
     vars=["r", "f"],
     hyps=[lambda v: v["r"] >= 0, lambda v: v["r"] <= 1,
           lambda v: v["f"] >= 0, lambda v: v["f"] <= 1],
     concl=lambda v: v["r"] * (1 - v["f"]) <= v["r"])

stmt(key="calib-missing-upper-bound", fqn="", verdict="FALSE",
     witness={"a": 1, "b": 2},
     note=("a>=0, b>=0 -> ab <= a, which needs b<=1. The shape of a dropped "
           "hypothesis. NOTE: the first draft of this case used b<=1 as the "
           "hypothesis, which makes the claim TRUE; the instrument correctly "
           "said HOLDS and the CASE was wrong. Kept as written to record that "
           "the calibration has itself been calibrated."),
     vars=["a", "b"],
     hyps=[lambda v: v["a"] >= 0, lambda v: v["b"] >= 0],
     concl=lambda v: v["a"] * v["b"] <= v["a"])

stmt(key="calib-off-by-constant", fqn="", verdict="FALSE",
     witness={"a": 1, "b": 1},
     note=("(a+b)^2 <= 2(a^2+b^2) is true and tight at a=b; at 1.9 it is "
           "false. Catches a wrong CONSTANT, not a wrong shape."),
     vars=["a", "b"],
     hyps=[lambda v: v["a"] > 0, lambda v: v["b"] > 0],
     concl=lambda v: (v["a"] + v["b"]) ** 2 * 10 <= 19 * (v["a"] ** 2 + v["b"] ** 2))

stmt(key="calib-boundary-only", fqn="", verdict="FALSE",
     witness={"r": "1/2"},
     note=("0<=r<=1 -> r^2 >= r holds at both endpoints and fails strictly "
           "inside. Catches the failure mode a boundary-only sampler misses."),
     vars=["r"],
     hyps=[lambda v: v["r"] >= 0, lambda v: v["r"] <= 1],
     concl=lambda v: v["r"] ** 2 >= v["r"])

stmt(key="calib-vacuous", fqn="", verdict="VACUOUS",
     note="Contradictory hypotheses. Anything at all follows.",
     vars=["f"],
     hyps=[lambda v: v["f"] > 0, lambda v: v["f"] < 0],
     concl=lambda v: v["f"] == 12345)


# ===========================================================================
# 2. CORPUS STATEMENTS.
# ===========================================================================

# `am_correction_increases_portability` after the differential-AM correction
# was inverted (commit cd95052a).  Recorded in BOTH forms because the pair is
# the evidence: the premise that is load-bearing depends on which way the
# correction runs, and an unused-premise scan computed against one form is
# wrong about the other.
#
# The divisor is now `1 - r_s*h2`, so the SOURCE stability condition is the
# necessary one.  With only the target condition the divisor is unconstrained
# and the statement is false.

stmt(key="am-correction-raises-portability", verdict="HOLDS",
     fqn="Calibrator.am_correction_increases_portability",
     note=("As it now stands: source stability condition present. "
           "port_m < port_m*(1-r_t*h2)/(1-r_s*h2)."),
     vars=["port_m", "r_s", "r_t", "h2"],
     hyps=[lambda v: v["port_m"] > 0,
           lambda v: v["h2"] > 0,
           lambda v: v["r_t"] < v["r_s"],
           lambda v: v["r_s"] * v["h2"] < 1],
     concl=lambda v: v["port_m"]
     < v["port_m"] * (1 - v["r_t"] * v["h2"]) / (1 - v["r_s"] * v["h2"]))

stmt(key="am-correction-with-target-condition-only", verdict="FALSE",
     fqn="Calibrator.am_correction_increases_portability",
     witness={"port_m": 1, "h2": 1, "r_t": 0, "r_s": 2},
     note=("PINNED AS FALSE ON PURPOSE. This is the same theorem with the "
           "TARGET stability condition substituted for the source one, which "
           "is how it stood transiently while two sessions edited it at once. "
           "The divisor 1-r_s*h2 is then unconstrained: at r_s=2, h2=1 it is "
           "-1 and the corrected value -1 is BELOW port_m. If this entry ever "
           "reports HOLDS, either the encoding broke or somebody added a "
           "hypothesis that quietly rules the witness out -- both are "
           "regressions, which is why a known-false statement is pinned rather "
           "than deleted."),
     vars=["port_m", "r_s", "r_t", "h2"],
     hyps=[lambda v: v["port_m"] > 0,
           lambda v: v["h2"] > 0,
           lambda v: v["r_t"] < v["r_s"],
           lambda v: v["r_t"] * v["h2"] < 1],
     concl=lambda v: v["port_m"]
     < v["port_m"] * (1 - v["r_t"] * v["h2"]) / (1 - v["r_s"] * v["h2"]))

stmt(key="three-way-ceiling", verdict="HOLDS",
     fqn="Calibrator.three_way_ceiling",
     note="A product of three unit-interval factors bounds a target R2 by 1.",
     vars=["h2", "gwas_power", "port_ratio", "target_r2"],
     hyps=[lambda v: v["h2"] <= 1, lambda v: v["gwas_power"] <= 1,
           lambda v: v["port_ratio"] <= 1, lambda v: v["h2"] >= 0,
           lambda v: v["gwas_power"] >= 0, lambda v: v["port_ratio"] >= 0,
           lambda v: v["target_r2"]
           <= v["h2"] * v["gwas_power"] * v["port_ratio"]],
     concl=lambda v: v["target_r2"] <= 1)

stmt(key="am-ld-breaks-cross-population", verdict="HOLDS",
     fqn="Calibrator.am_ld_breaks_cross_population",
     note=("r_t(1-r_s h2) < r_s(1-r_t h2). The assortment term cancels off "
           "both sides, leaving r_t < r_s, so h2 does not enter. Transcribed "
           "to record that the cancellation is real and the premise set is "
           "genuinely one hypothesis."),
     vars=["r_s", "r_t", "h2"],
     hyps=[lambda v: v["r_t"] < v["r_s"]],
     concl=lambda v: v["r_t"] * (1 - v["r_s"] * v["h2"])
     < v["r_s"] * (1 - v["r_t"] * v["h2"]))
