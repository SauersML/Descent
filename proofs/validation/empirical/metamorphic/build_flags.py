#!/usr/bin/env python3
"""Guard the build configuration against flags that silently change the maths.

    python3 proofs/validation/empirical/metamorphic/build_flags.py

WHY THIS EXISTS.  The scoring kernel's arithmetic is part of the specification:
`score/kernel.rs` accumulates each score column in a separate `f32x8` lane in
variant order, and `score/batch.rs` flushes to an `f64` master every
KERNEL_MINI_BATCH_SIZE variants.  That design is what makes the score
reproducible and its error independent of the variant count.  A single build
flag can dissolve it without touching a line of the source:

  * `-ffast-math` / LLVM `reassoc` lets the compiler re-associate the
    accumulation, which reorders a sum the mathematics assumes is taken in a
    fixed order -- the score then depends on how the optimiser felt.
  * `nnan`/`ninf` deletes the NaN and infinity propagation that carries a
    missing genotype through to the output instead of silently scoring it.
  * a reduced-precision or reciprocal-approximation flag demotes arithmetic the
    model assumes is IEEE f32/f64.

None of these produce a source diff, none produce a test failure on small
inputs, and all of them are one innocent-looking line in `.cargo/config.toml`.
This check is cheap, has no dependencies, and would have caught the change.

WHAT WAS MEASURED, so that this is a regression guard and not a superstition.
The kernel was compiled and its aarch64 assembly and LLVM IR read by hand at
commit 0449db90.  Findings, all clean, recorded here as the baseline:

  * zero fast-math flags on any FP instruction in the IR: no `fast`, `reassoc`,
    `nsz`, `ninf`, `nnan`, `arcp` or `afn`.
  * no `unsafe-fp-math` / `no-nans-fp-math` / `no-infs-fp-math` function
    attributes.
  * the dosage-1 loop lowers to sixteen INDEPENDENT four-lane accumulators
    (`fadd.4s` into v0-v7 and v16-v23), one per score column, each summing its
    own column in variant order. No cross-lane reduction, so nothing reorders a
    sum.
  * the dosage-2 loop lowers to `llvm.fma.v8f32(w, splat(2.0), acc)`, i.e.
    `fmla.4s` against an immediate 2.0. This is exactly what the doc comment at
    score/kernel.rs:20-32 claims, and the claim is correct: `2*w` is exact in
    IEEE-754, so `fma(w, 2, acc)` and `acc + (w + w)` each round once and agree
    bit for bit.
  * no f32 where the model assumes f64: the f32 accumulator is deliberate and
    bounded by the 256-variant flush, and `f32 -> f64` widening is exact.

MEASURED CONSEQUENCE of the design this protects: emulating the shipped
arithmetic, accumulation error against an exact `fsum` reference is flat at
~1e-7 of a cohort SD from M=1e4 to M=1e6 variants -- it does NOT grow with the
variant count -- and the spread over variant permutations is ~5e-7 SD. Removing
only the f64 flush (pure f32 accumulation) makes the permutation spread grow
with M to 1.2e-5 SD. The flush is load-bearing; KERNEL_MINI_BATCH_SIZE is
checked below so that raising it does not quietly undo that.
"""

import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "..", "..", "..", ".."))

# Flags that change the mathematics. Matched against build configuration only,
# never against prose.
FORBIDDEN = (
    ("ffast-math", "re-associates FP arithmetic and drops NaN/inf handling"),
    ("funsafe-math-optimizations", "licenses algebraically invalid rewrites"),
    ("fno-honor-nans", "deletes the NaN propagation that carries missingness"),
    ("fno-honor-infinities", "deletes infinity propagation"),
    ("ffinite-math-only", "assumes no NaN and no inf"),
    ("freciprocal-math", "replaces division by reciprocal multiplication"),
    ("fassociative-math", "re-associates the accumulation order"),
    ("enable-unsafe-fp-math", "LLVM's unsafe FP mode"),
    ("fp-contract=fast", "contracts across statements, changing rounding"),
)

# Source-level opt-ins to the same thing.
FORBIDDEN_SOURCE = (
    ("f32::algebraic_add", "algebraic float ops permit reassociation"),
    ("f32::algebraic_mul", "algebraic float ops permit reassociation"),
    ("f64::algebraic_add", "algebraic float ops permit reassociation"),
    ("f64::algebraic_mul", "algebraic float ops permit reassociation"),
    ("fadd_fast", "LLVM fast-math intrinsic"),
    ("fmul_fast", "LLVM fast-math intrinsic"),
)

CONFIG_FILES = (
    ".cargo/config.toml",
    ".cargo/config",
    "Cargo.toml",
    "rust-toolchain.toml",
)

KERNEL = "score/kernel.rs"
BATCH = "score/batch.rs"

findings = []


def read(rel):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as handle:
        return handle.read()


def check_configs():
    for rel in CONFIG_FILES:
        text = read(rel)
        if text is None:
            continue
        for flag, why in FORBIDDEN:
            if flag in text:
                findings.append(
                    f"{rel}: build flag {flag!r} is present. {why}. The scoring "
                    f"kernel's accumulation order and NaN handling are part of "
                    f"the specification; see this file's header for the "
                    f"assembly-level baseline it would break.")
    # RUSTFLAGS in the workflow files, where it is equally invisible.
    wf = os.path.join(ROOT, ".github", "workflows")
    if os.path.isdir(wf):
        for name in sorted(os.listdir(wf)):
            if not name.endswith((".yml", ".yaml")):
                continue
            text = read(os.path.join(".github", "workflows", name)) or ""
            for flag, why in FORBIDDEN:
                if flag in text:
                    findings.append(
                        f".github/workflows/{name}: build flag {flag!r}. {why}.")


def check_sources():
    for rel in (KERNEL, BATCH):
        text = read(rel)
        if text is None:
            findings.append(f"MISSING: {rel} does not exist; this guard is "
                            f"pinned to a file that moved.")
            continue
        for token, why in FORBIDDEN_SOURCE:
            if token in text:
                findings.append(f"{rel}: uses {token}. {why}.")


def check_kernel_shape():
    """The two properties the measured error bound depends on."""
    kernel = read(KERNEL)
    batch = read(BATCH)
    if kernel is None or batch is None:
        return

    # 1. The accumulator is f32x8 and the widening target is f64. Anchored to
    #    the declaration, not to a line number.
    if not re.search(r"pub\s+type\s+SimdVec\s*=\s*f32x8", kernel):
        findings.append(
            f"{KERNEL}: SimdVec is no longer declared as f32x8. The measured "
            f"~1e-7 cohort-SD error bound is specific to f32 accumulation "
            f"flushed to f64; re-measure before changing this.")

    # 2. The flush period. The error bound is flat in the variant count ONLY
    #    because the f32 accumulator is drained often. Pure f32 accumulation
    #    was measured at 1.2e-5 cohort SD and growing with M.
    m = re.search(r"KERNEL_MINI_BATCH_SIZE\s*:\s*usize\s*=\s*(\d+)", batch)
    if m is None:
        findings.append(
            f"{BATCH}: KERNEL_MINI_BATCH_SIZE is gone. It is the flush period "
            f"that bounds f32 accumulation error independently of the variant "
            f"count.")
    else:
        size = int(m.group(1))
        if size > 4096:
            findings.append(
                f"{BATCH}: KERNEL_MINI_BATCH_SIZE = {size}. The f32 accumulator "
                f"is drained to f64 only every {size} variants; the error bound "
                f"measured for this design assumed a few hundred. Re-measure "
                f"the permutation spread before raising it further.")

    # 3. The doubling in the dosage-2 path must stay a single rounding. Both
    #    `mul_add(2.0, acc)` and `acc + (w + w)` are single-rounding and agree
    #    bit for bit; a plain `2.0 * w + acc` written as two operations would
    #    not be the thing the doc comment claims.
    if "mul_add" not in kernel and "w + w" not in kernel:
        findings.append(
            f"{KERNEL}: neither the fused nor the doubling form of the dosage-2 "
            f"accumulation is present. The bit-for-bit equivalence documented "
            f"at the top of that file no longer describes the code.")


def main():
    check_configs()
    check_sources()
    check_kernel_shape()
    print("build-configuration guard: "
          f"{len(CONFIG_FILES)} config files, {len(FORBIDDEN)} forbidden flags, "
          f"kernel shape anchored to declarations.")
    if findings:
        print(f"\n{len(findings)} FINDING(S):\n")
        for f in findings:
            print("  " + f)
        return 1
    print("no fast-math or reassociation licence anywhere in the build "
          "configuration; kernel accumulation shape unchanged.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
