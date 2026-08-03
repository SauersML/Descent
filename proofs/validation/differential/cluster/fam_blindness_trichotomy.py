#!/usr/bin/env python3
"""Family simulator: THREE BLINDNESS INSTANCES. numpy only.

FIRST CONTACT BETWEEN Sec. 15 OF FoldedSpectrum.lean AND ANY NUMBER.
The Lean module now labels symmetry, isolated coincidence, and support loss as a
TAXONOMY, not an exhaustive classification. This script compares one concrete
instance of each. Distinct responses in these examples do not prove that every
blind observation map belongs to one of three classes.

SCOPE, SO THIS DOES NOT DUPLICATE WORK ALREADY RUNNING
    `fam_ensemble_channel.py` covers Sec. 14: the channel T1, the depth sweep
    T1b against the mixing time, off-zero invisibility T2, deconvolution T3, the
    curve-prior identity T4 and the exact limit T5, with controls C1-C5.  None
    of it touches Sec. 15.  This file tests ONLY the trichotomy, on the diploid
    bundle family that Sec. 1-2 of the same module defines, and it re-derives no
    channel quantity.

WHAT THE CORPUS CLAIMS (FoldedSpectrum.lean Sec. 15)

  B1  SYMMETRY blindness.  The observation factors through a gauge action and
      the invisible set is the ORBIT TANGENT.  Instance: the folded spectrum.
      `foldedSpectrum_gauge` proves the modulus law of a panel equals that of
      its reflection q <-> 1-q, for EVERY q.

  B2  RESONANCE blindness.  No gauge acts; kernels live only on ARITHMETIC or
      dynamical resonance sets and the direction is not predictable a priori.
      Instance: the balanced locus.  `diploid_modulus_at_half` proves all three
      moduli equal 1 at q = 1/2, and
      `diploid_modulus_degenerate_only_at_half` proves this happens NOWHERE
      ELSE in (0,1).

  B3  SUPPORT blindness.  Resonance made TOTAL by a vanishing-support
      condition.  Instance: two loci at the same frequency -- eta = 0, perfect
      LD.  `frequencyTie_gives_kernel` proves the weight split between them is
      invisible at every modulus value.

  B4  AN EXPLORATORY COMPLETION PROBE. A proposed collapse principle says that
      an isolated analytic resonance is broken by a generic band shift unless
      it comes from a persistent identity. One random shift of one genotype
      instance is a falsifier and development check, never evidence for the
      universal principle.

THE DISCRIMINATING EXPERIMENT
    A band shift sends the three modulus values m_j -> m_j + delta_j.  Take
    delta EQUIVARIANT (delta_0 = delta_2), so the shift itself respects the
    reflection gauge and cannot be accused of destroying B1 by brute force.
    Then the three classes are predicted to respond differently:

        instance   equivariant generic band shift   tie broken   wrong gauge map
        symmetry   survives                         n/a          dies
        resonance  DIES                             n/a          n/a
        support    survives                         DIES         n/a

    These rows describe these three witnesses only. If the resonance survives
    the shift, this instance refutes the proposed generic-breaking story; if it
    dies, the universal claim remains open.

WITNESS PLACEMENT: THE CLAIM SAYS "EXCEPT ON S", SO THE WITNESS GOES IN S
    B2's content is an EXCEPT: non-degenerate everywhere in (0,1) EXCEPT at
    q = 1/2.  A degeneracy probe at q = 0.3 tests nothing, because both the
    corpus and its negation predict non-degeneracy there.  Every resonance
    witness below therefore sits AT q = 1/2, with the off-witnesses placed
    immediately beside it to measure how fast the coincidence dies.

    This is the defect that `neiGst_ne_trueHudsonFst` had: it sat at
    pbar = 2/5 and so could not exclude the pbar = 1/2 slice its own claim
    named.  It failed fine -- at a point nobody disputed.

THE MUTATION GATE IS THE POINT OF THE FILE
    A simulation that passes against correct code and also passes against
    corrupted code has measured nothing.  Every PASS below is paired with a
    MUTANT of the quantity it depends on, and the run FAILS unless the mutant is
    REJECTED.  `mutation_gate` prints one line per mutant whether it fires or
    not, and the exit status is non-zero if any mutant survived.

    One mutant is reported as SURVIVING BY DESIGN and is not counted as a
    failure: dropping the absolute value from the modulus does NOT break the
    symmetry check, because the reflection negates the standardized dosage and
    the square is taken before the absolute value.  That is a true statement
    about what the symmetry test can and cannot detect, and hiding it would
    overstate the gate.
"""

import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "fam_blindness_trichotomy_results.json")

# Tolerance. Deliberately tight, and near-ties are REPORTED rather than merged:
# this corpus has already recorded one false positive from a 1e-9 tolerance that
# merged (3-sqrt(3))/6 with a decimal approximation straddling a sign change.
TOL = 1e-11
NEAR_TIE = 1e-7


# ---------------------------------------------------------------- the family

def atom_values(q):
    """Standardized dosages a_j(q) = (j - 2q)/sqrt(2q(1-q)), j = 0,1,2."""
    s = np.sqrt(2.0 * q * (1.0 - q))
    return np.array([(j - 2.0 * q) / s for j in (0, 1, 2)])


def atom_masses(q):
    """Hardy-Weinberg masses, locked to the single parameter q."""
    return np.array([(1.0 - q) ** 2, 2.0 * q * (1.0 - q), q ** 2])


def moduli(q, use_abs=True, shift=None):
    """Modulus curve m_j(q) = |a_j(q)^2 - 1|, optionally band-shifted.

    `shift` is a length-3 band shift added AFTER the modulus is formed.
    `use_abs=False` is the mutant that drops the absolute value.
    """
    a = atom_values(q)
    m = a ** 2 - 1.0
    m = np.abs(m) if use_abs else m
    if shift is not None:
        m = m + np.asarray(shift, dtype=float)
    return m


def mass_at(q, reflect=None, use_abs=True, shift=None, mass_permute=True):
    """The (value, mass) pairs a locus at q puts on the modulus axis.

    Returned sorted by value, which is what makes it an ORDER-FREE object: the
    modulus law is a multiset, and the genotype labels are not observable.

    `reflect` applies a candidate gauge map to q before evaluating.
    `mass_permute=False` is the mutant that permutes the values under
    reflection but NOT the masses.
    """
    qq = reflect(q) if reflect is not None else q
    m = moduli(qq, use_abs=use_abs, shift=shift)
    w = atom_masses(qq) if mass_permute else atom_masses(q)
    return canonical_law(m, w)


def canonical_law(m, w):
    """Canonical form of a modulus law: sorted values with TIED VALUES MERGED.

    Merging is not tidying, it is the definition.  The modulus law is a measure
    on the value axis, so two atoms landing on the same value are one atom of
    combined mass, and any representation that keeps them apart depends on a
    genotype label the observer does not have.

    THIS FILE'S FIRST RUN GOT THIS WRONG AND THE ERROR LOOKED LIKE A REFUTATION.
    Sorting by value and comparing mass vectors elementwise reported the folded
    spectrum failing by 3/16 = 0.1875.  The whole discrepancy came from q = 1/4,
    where m_0 = m_1 = 1/3 exactly: with two equal values, argsort breaks the tie
    by index, the index order is reversed between q and 1-q, and the masses
    0.5625 and 0.375 were subtracted in the wrong pairing.  The theorem was fine
    and the harness was wrong -- and the within-locus tie at q = 1/4 is a real
    feature of this family, not a numerical accident, so the harness had to
    handle it rather than avoid it.
    """
    order = np.argsort(m, kind="stable")
    m = np.asarray(m, dtype=float)[order]
    w = np.asarray(w, dtype=float)[order]
    vals, mass = [], []
    for v, u in zip(m, w):
        if vals and abs(v - vals[-1]) < NEAR_TIE:
            mass[-1] += u
        else:
            vals.append(v)
            mass.append(u)
    return np.array(vals), np.array(mass)


def law_distance(q1, q2, **kw):
    """Distance between two loci's canonical modulus laws."""
    m1, w1 = mass_at(q1, **kw)
    m2, w2 = mass_at(q2, **kw)
    return compare_laws(m1, w1, m2, w2)


# ------------------------------------------------------- B1 symmetry instance

def test_symmetry(qs, shift=None, gauge=None, mass_permute=True):
    """Is the modulus law invariant under the gauge map, across a whole grid?

    Symmetry blindness is an OPEN condition -- it holds on a set with interior,
    not at isolated points -- so the test sweeps q and reports the worst case.
    """
    gauge = gauge if gauge is not None else (lambda q: 1.0 - q)
    worst = 0.0
    for q in qs:
        m1, w1 = mass_at(q, shift=shift, mass_permute=True)
        m2, w2 = mass_at(q, reflect=gauge, shift=shift, mass_permute=mass_permute)
        worst = max(worst, compare_laws(m1, w1, m2, w2))
    return worst


def compare_laws(m1, w1, m2, w2):
    """Distance between two canonical modulus laws.

    Different atom counts means the two measures are supported on different
    numbers of points, which is a maximal disagreement, not a shape mismatch to
    be padded away.
    """
    if len(m1) != len(m2):
        return float("inf")
    if len(m1) == 0:
        return 0.0
    if not (np.all(np.isfinite(m1)) and np.all(np.isfinite(m2))):
        return float("inf")
    return float(max(np.max(np.abs(m1 - m2)), np.max(np.abs(w1 - w2))))


# ------------------------------------------------------ B2 resonance instance

def degeneracy(q, shift=None):
    """Spread of the three modulus values. Zero exactly at a resonance."""
    m = moduli(q, shift=shift)
    return float(np.max(m) - np.min(m))


# -------------------------------------------------------- B3 support instance

def tie_kernel_residual(q_a, q_b, c=1.0, shift=None, grid=None):
    """Modulus signal of the panel {(q_a, +c), (q_b, -c)}.

    Sec. 4 `frequencyTie_gives_kernel`: when q_a == q_b this is identically zero
    at EVERY modulus value -- the weight split is invisible.  The residual below
    is the largest signal over a grid of probe values, so zero means invisible.
    """
    ma, wa = mass_at(q_a, shift=shift)
    mb, wb = mass_at(q_b, shift=shift)
    probes = np.unique(np.concatenate([ma, mb])) if grid is None else grid
    worst = 0.0
    for v in probes:
        sa = float(np.sum(wa[np.abs(ma - v) < TOL]))
        sb = float(np.sum(wb[np.abs(mb - v) < TOL]))
        worst = max(worst, abs(c * sa - c * sb))
    return worst


# --------------------------------------------------------------- experiments

def run_instances():
    """The three instances, each at the place its own claim is contested."""
    out = {}
    rng = np.random.default_rng(20260802)

    grid = np.linspace(0.02, 0.98, 193)
    grid = grid[np.abs(grid - 0.5) > 1e-9]

    # ---- B1 SYMMETRY: holds on an open set, so sweep.
    sym_unshifted = test_symmetry(grid)
    out["B1_symmetry_worst_deviation"] = sym_unshifted
    out["B1_symmetry_holds"] = bool(sym_unshifted < 1e-9)

    # ---- B2 RESONANCE: witness AT q = 1/2, which is the excepted set S.
    deg_at_half = degeneracy(0.5)
    out["B2_degeneracy_at_half"] = deg_at_half
    out["B2_resonance_present_at_half"] = bool(deg_at_half < 1e-12)

    # How fast does it die beside the witness?  This is what makes it ISOLATED
    # rather than an open condition, and it is the difference from B1.
    beside = []
    for eps in (1e-4, 1e-3, 1e-2, 1e-1):
        beside.append({"eps": eps,
                       "degeneracy": degeneracy(0.5 + eps),
                       "degeneracy_minus": degeneracy(0.5 - eps)})
    out["B2_beside_the_witness"] = beside
    out["B2_isolated"] = bool(all(b["degeneracy"] > 1e-9 for b in beside))

    # ---- B3 SUPPORT: the tie, and the tie broken.
    tied = tie_kernel_residual(0.3, 0.3)
    untied = tie_kernel_residual(0.3, 0.3001)
    out["B3_tied_residual"] = tied
    out["B3_untied_residual"] = untied
    out["B3_support_blind_when_tied"] = bool(tied < 1e-12)
    out["B3_visible_when_tie_broken"] = bool(untied > 1e-9)

    return out, rng, grid


def run_band_shift(rng, grid):
    """B4: ONE generic EQUIVARIANT band shift, applied to all three instances.

    Equivariant means delta_0 = delta_2, so the shift commutes with the genotype
    relabelling the gauge acts by.  This is the fair version of the test: a
    non-equivariant shift would destroy B1 mechanically and prove nothing.
    """
    out = {}
    d0, d1 = rng.normal(scale=0.37, size=2)
    shift = np.array([d0, d1, d0])
    out["shift"] = [float(x) for x in shift]

    out["B1_after_shift_worst_deviation"] = test_symmetry(grid, shift=shift)
    out["B1_survives_shift"] = bool(out["B1_after_shift_worst_deviation"] < 1e-9)

    out["B2_degeneracy_at_half_after_shift"] = degeneracy(0.5, shift=shift)
    out["B2_dies_under_shift"] = bool(out["B2_degeneracy_at_half_after_shift"] > 1e-9)

    out["B3_tied_residual_after_shift"] = tie_kernel_residual(0.3, 0.3, shift=shift)
    out["B3_survives_shift"] = bool(out["B3_tied_residual_after_shift"] < 1e-12)

    # The discriminating table, as booleans, in the order the docstring predicts.
    out["table"] = {
        "symmetry_survives_shift": out["B1_survives_shift"],
        "resonance_survives_shift": not out["B2_dies_under_shift"],
        "support_survives_shift": out["B3_survives_shift"],
    }
    out["three_distinct_rows"] = bool(
        out["B1_survives_shift"] and out["B2_dies_under_shift"] and out["B3_survives_shift"]
    )
    return out


def mutation_gate(grid):
    """Every claim above, re-run against a CORRUPTED body. Mutants must be rejected.

    A mutant that SURVIVES means the corresponding test cannot tell correct code
    from broken code, and the gate fails.  One survivor is expected and declared.
    """
    results = []

    # M1: wrong gauge map.  q -> 0.9 - q is not the reflection.
    # Chosen to stay inside (0,1) on the whole grid, so the mutant is rejected
    # for being the wrong map and not for producing NaN.
    dev = test_symmetry(grid, gauge=lambda q: 1.0 - 0.9 * q)
    results.append({"mutant": "M1_wrong_gauge_map_1_minus_0.9q",
                    "statistic": dev, "rejected": bool(dev > 1e-6),
                    "expected_rejected": True})

    # M2: values permuted under reflection but masses NOT permuted.
    dev = test_symmetry(grid, mass_permute=False)
    results.append({"mutant": "M2_masses_not_permuted",
                    "statistic": dev, "rejected": bool(dev > 1e-6),
                    "expected_rejected": True})

    # M3: resonance witness moved OUT of the excepted set S = {1/2}.  This is
    # the neiGst defect reproduced deliberately: a probe at q = 0.3 cannot
    # distinguish the corpus from its negation, so a test sited there is
    # uninformative and must NOT be counted as evidence.
    deg = degeneracy(0.3)
    results.append({"mutant": "M3_resonance_probe_outside_S_at_q_0.3",
                    "statistic": deg, "rejected": bool(deg > 1e-9),
                    "expected_rejected": True,
                    "note": "rejection here means the probe would have found "
                            "no resonance, i.e. siting the witness outside S "
                            "tests nothing"})

    # M4: support instance with the tie broken.
    res = tie_kernel_residual(0.3, 0.31)
    results.append({"mutant": "M4_tie_broken",
                    "statistic": res, "rejected": bool(res > 1e-9),
                    "expected_rejected": True})

    # M5: DECLARED SURVIVOR.  Dropping the absolute value does not break the
    # symmetry test, because reflection negates the dosage and the square is
    # taken first.  Reported so the gate is not overstated.
    dev = test_symmetry(grid)
    dev_noabs = 0.0
    for q in grid:
        m1, w1 = mass_at(q, use_abs=False)
        m2, w2 = mass_at(q, reflect=lambda x: 1.0 - x, use_abs=False)
        dev_noabs = max(dev_noabs, float(np.max(np.abs(m1 - m2))))
    results.append({"mutant": "M5_modulus_without_absolute_value",
                    "statistic": dev_noabs, "rejected": bool(dev_noabs > 1e-6),
                    "expected_rejected": False,
                    "note": "SURVIVES BY DESIGN: the symmetry test is blind to "
                            "this mutation, because a_j(1-q) = -a_{2-j}(q) and "
                            "the square precedes the absolute value. Declared "
                            "rather than hidden."})

    gate_pass = all(r["rejected"] == r["expected_rejected"] for r in results)
    return results, gate_pass


def main():
    print("FAMILY: THREE BLINDNESS INSTANCES  (FoldedSpectrum.lean Sec. 15)")
    print("=" * 70)

    inst, rng, grid = run_instances()
    print("\nB1 SYMMETRY (folded spectrum, swept over %d frequencies)" % len(grid))
    print("   worst deviation over the grid: %.3e  -> holds: %s"
          % (inst["B1_symmetry_worst_deviation"], inst["B1_symmetry_holds"]))

    print("\nB2 RESONANCE (witness AT q = 1/2, inside the excepted set)")
    print("   degeneracy at q = 1/2: %.3e  -> resonance present: %s"
          % (inst["B2_degeneracy_at_half"], inst["B2_resonance_present_at_half"]))
    for b in inst["B2_beside_the_witness"]:
        print("   beside it, eps = %-7g : %.3e / %.3e"
              % (b["eps"], b["degeneracy"], b["degeneracy_minus"]))
    print("   isolated (dies immediately off the witness): %s" % inst["B2_isolated"])

    print("\nB3 SUPPORT (two loci tied at q = 0.3)")
    print("   tied residual:   %.3e -> invisible: %s"
          % (inst["B3_tied_residual"], inst["B3_support_blind_when_tied"]))
    print("   tie broken:      %.3e -> visible:   %s"
          % (inst["B3_untied_residual"], inst["B3_visible_when_tie_broken"]))

    shift = run_band_shift(rng, grid)
    print("\nB4 ONE GENERIC EQUIVARIANT BAND SHIFT  delta = [%.4f, %.4f, %.4f]"
          % tuple(shift["shift"]))
    print("   symmetry  after shift: %.3e -> survives: %s"
          % (shift["B1_after_shift_worst_deviation"], shift["B1_survives_shift"]))
    print("   resonance after shift: %.3e -> dies:     %s"
          % (shift["B2_degeneracy_at_half_after_shift"], shift["B2_dies_under_shift"]))
    print("   support   after shift: %.3e -> survives: %s"
          % (shift["B3_tied_residual_after_shift"], shift["B3_survives_shift"]))
    print("   THREE DISTINCT RESPONSE ROWS IN THESE WITNESSES: %s"
          % shift["three_distinct_rows"])

    mutants, gate_pass = mutation_gate(grid)
    print("\nMUTATION GATE")
    for m in mutants:
        status = "REJECTED" if m["rejected"] else "SURVIVED"
        ok = "ok" if m["rejected"] == m["expected_rejected"] else "GATE FAILURE"
        print("   %-42s %-9s (%.3e)  %s" % (m["mutant"], status, m["statistic"], ok))
    print("   gate pass: %s" % gate_pass)

    verdict = {
        "instances": inst,
        "band_shift": shift,
        "mutation_gate": {"mutants": mutants, "pass": gate_pass},
        "headline": {
            "three_witnesses_have_distinct_rows": shift["three_distinct_rows"],
            "one_shift_breaks_this_resonance_witness":
                shift["B2_dies_under_shift"],
            "gate_pass": gate_pass,
        },
    }
    with open(OUT, "w") as fh:
        json.dump(verdict, fh, indent=2)
    print("\nwrote %s" % OUT)

    if not gate_pass:
        print("\nEXIT NON-ZERO: a mutant survived, so at least one test above "
              "cannot distinguish correct code from corrupted code.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
