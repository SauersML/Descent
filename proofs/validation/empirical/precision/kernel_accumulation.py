#!/usr/bin/env python3
"""A NEGATIVE RESULT, preserved so it is not re-derived: the shipped scoring
kernel's mixed f32/f64 accumulation is accurate enough, and here is the
threshold that would have condemned it.

    python3 proofs/validation/empirical/precision/kernel_accumulation.py

Needs numpy, so it is not in the required set; the committed CONCLUSION is
guarded cheaply and without dependencies by
`empirical/metamorphic/build_flags.py`, which pins the two constants this
measurement depends on. This script is how those constants were justified and
how to re-justify them if either moves.

WHAT IS EMULATED, and where each detail comes from:

    score/pipeline.rs   weights are f32 (`weights: &'a mut [f32]`)
    score/kernel.rs:16  per-person accumulation is f32x8
    score/batch.rs:35   the kernel runs on KERNEL_MINI_BATCH_SIZE = 256 variants
    score/kernel.rs:144 inside a mini-batch ALL dosage-1 variants are summed
    score/kernel.rs:160 first, then all dosage-2 variants -- so the summation
                        order is not the variant order
    score/batch.rs:185  each mini-batch result is widened f32 -> f64 (exact) and
                        added to an f64 master accumulator

THE RELATION UNDER TEST is metamorphic and needs no oracle: permuting the
variant order must leave every individual's score unchanged.  Over the reals it
does, exactly.  The question is only what the implementation does, and the
answer has to be read against the scale a PGS is actually used on -- a cohort
standard deviation, since scores are consumed as z-scores and percentiles -- not
against the score's own magnitude, which is a near-cancelling sum and can sit
arbitrarily close to zero.

CALIBRATION, both directions, because a permutation spread of "about zero" is
not evidence until something is shown to make it non-zero:

    pure f64, same term order        spread EXACTLY 0.0        (control)
    shipped f32 + 256-variant flush  ~5e-7 cohort SD, FLAT in M
    planted: flush removed           grows with M to 1.2e-5 SD (would condemn)

MEASURED at commit 0449db90, M = 10^4, 10^5, 10^6 variants:

    M          error/SD    permutation spread/SD    no-flush plant/SD
    10^4       1.04e-07    4.94e-07                 9.57e-07
    10^5       1.16e-07    3.66e-07                 1.18e-05
    10^6       1.02e-07    7.93e-07                 6.79e-06

The load-bearing observation is that the shipped columns do NOT grow with M
while the plant's does.  That is the f64 master absorbing each mini-batch before
the f32 accumulator can drift, and it is why KERNEL_MINI_BATCH_SIZE is a
correctness constant and not only a cache-tuning one.

VERDICT: the design survives. Raising the flush period, widening the accumulator
window, or removing the f64 master would each invalidate this, which is what
build_flags.py checks for cheaply on every CI run.
"""

import math
import sys

try:
    import numpy as np
except ImportError:                                          # pragma: no cover
    print("kernel_accumulation: numpy not installed; this instrument is not in "
          "the required set. Its conclusion is guarded by "
          "empirical/metamorphic/build_flags.py.")
    sys.exit(0)

MINI_BATCH = 256          # score/batch.rs:35 KERNEL_MINI_BATCH_SIZE
COHORT = 400              # individuals used to estimate the score's SD


def score_shipped(dos, w, mini_batch=MINI_BATCH, flush=True):
    """The shipped arithmetic for one person, one score column."""
    master = np.float64(0.0)
    acc32 = np.float32(0.0)
    for start in range(0, len(w), mini_batch):
        d = dos[start:start + mini_batch]
        ww = w[start:start + mini_batch]
        if flush:
            acc32 = np.float32(0.0)
        for x in ww[d == 1]:                       # kernel.rs:144, dosage-1 loop
            acc32 = np.float32(acc32 + x)
        for x in ww[d == 2]:                       # kernel.rs:160, dosage-2 loop
            acc32 = np.float32(acc32 + np.float32(2.0) * x)
        if flush:
            master += np.float64(acc32)            # batch.rs:185, exact widening
    return master if flush else np.float64(acc32)


def score_f64(dos, w):
    """Control: identical term order, f64 accumulator. Must be permutation-exact
    on this data, since every term is exactly representable."""
    acc = np.float64(0.0)
    for start in range(0, len(w), MINI_BATCH):
        d = dos[start:start + MINI_BATCH]
        ww = w[start:start + MINI_BATCH].astype(np.float64)
        for x in ww[d == 1]:
            acc += x
        for x in ww[d == 2]:
            acc += 2.0 * x
    return acc


def score_exact(dos, w):
    """f32 weights are exact binary rationals and dosages are integers, so
    math.fsum over the products is the true value with no rounding at all."""
    return math.fsum(float(w[i]) * int(dos[i]) for i in range(len(w)))


def panel(M, rng):
    """A realistic panel: MAF ~ U(0.01, 0.5) and per-variant effects scaled by
    1/sqrt(2p(1-p)) so every variant contributes equal trait variance."""
    maf = rng.uniform(0.01, 0.5, M)
    beta = rng.normal(0.0, 1.0 / np.sqrt(M), M)
    return maf, (beta / np.sqrt(2 * maf * (1 - maf))).astype(np.float32)


def run(M, nperm=6, seed=0):
    rng = np.random.default_rng(seed)
    maf, w = panel(M, rng)
    dos = rng.binomial(2, maf).astype(np.int8)

    truth = score_exact(dos, w)
    base_ship = score_shipped(dos, w)
    base_f64 = score_f64(dos, w)
    sd = np.array([score_exact(rng.binomial(2, maf).astype(np.int8), w)
                   for _ in range(COHORT)]).std()

    ship, nofl, f64 = [], [], []
    for _ in range(nperm):
        idx = rng.permutation(M)
        ship.append(score_shipped(dos[idx], w[idx]))
        nofl.append(score_shipped(dos[idx], w[idx], flush=False))
        f64.append(score_f64(dos[idx], w[idx]))

    def spread(vals, base):
        allv = np.concatenate([np.array(vals), [base]])
        return float(allv.max() - allv.min())

    return {
        "M": M, "sd": float(sd),
        "err": abs(base_ship - truth) / sd,
        "perm": spread(ship, base_ship) / sd,
        "nofl": spread(nofl, nofl[0]) / sd,
        "f64": spread(f64, base_f64),
    }


def main():
    rows = [run(M, seed=M) for M in (10_000, 100_000, 1_000_000)]

    print(f"{'M':>10} {'err/SD':>12} {'permSpread/SD':>15} "
          f"{'noFlush/SD':>13} {'f64 control':>13}")
    for r in rows:
        print(f"{r['M']:>10} {r['err']:12.3e} {r['perm']:15.3e} "
              f"{r['nofl']:13.3e} {r['f64']:13.3e}")

    findings = []
    for r in rows:
        if r["f64"] != 0.0:
            findings.append(
                f"M={r['M']}: the pure-f64 control has non-zero permutation "
                f"spread ({r['f64']:.3e}). The control is supposed to be exact "
                f"on this data; the emulation itself is wrong, so no verdict "
                f"below it means anything.")
        if r["nofl"] <= r["perm"]:
            findings.append(
                f"M={r['M']}: the planted no-flush defect ({r['nofl']:.3e} SD) "
                f"is no worse than the shipped design ({r['perm']:.3e} SD). "
                f"This measurement has no power to condemn a bad accumulator, "
                f"so its pass for the shipped one is not evidence.")
        if r["perm"] > 1e-4:
            findings.append(
                f"M={r['M']}: shipped permutation spread {r['perm']:.3e} cohort "
                f"SD exceeds 1e-4. The score now depends on variant order at a "
                f"level that could move a percentile. Check "
                f"KERNEL_MINI_BATCH_SIZE and the f64 master in score/batch.rs.")

    growth = rows[-1]["perm"] / max(rows[0]["perm"], 1e-30)
    print(f"\nshipped permutation spread grows {growth:.2f}x from M=1e4 to "
          f"M=1e6; the no-flush plant grows "
          f"{rows[-1]['nofl'] / max(rows[0]['nofl'], 1e-30):.2f}x.")

    if findings:
        print(f"\n{len(findings)} FINDING(S):\n")
        for f in findings:
            print("  " + f)
        return 1
    print("\nshipped f32/f64 accumulation survives: error and permutation "
          "spread both ~1e-7 cohort SD and flat in M; calibration plant "
          "correctly worse; f64 control exactly zero.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
