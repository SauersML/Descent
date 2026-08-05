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

# Filenames that can carry a flag into the build, ANYWHERE in the tree. This
# used to be four fixed paths at the repository root, which is not where cargo
# looks: `.cargo/config.toml` is honoured from every ancestor of the directory
# being built, each crate carries its own `Cargo.toml`, and a `build.rs` can
# emit `cargo:rustc-flags=...` at compile time. Measured: `-C
# llvm-args=-enable-unsafe-fp-math` planted in `calibrate/.cargo/config.toml`
# and in `shared/build.rs` produced zero findings and the guard printed "no
# fast-math or reassociation licence anywhere in the build configuration".
#
# Discovered rather than enumerated, for the reason stated all over this
# directory: a list of paths stops covering things silently, and this one had.
CONFIG_NAMES = (
    "config.toml",              # only under a .cargo/ directory; see below
    "config",                   # ditto, cargo's pre-2020 spelling
    "Cargo.toml",
    "rust-toolchain.toml",
    "rust-toolchain",
    "build.rs",
)

# Vendored and generated trees. A dependency's own Cargo.toml is not this
# repository's build configuration, and .venv carries megabytes of unrelated
# text.
SKIP_DIRS = (".git", "target", ".venv", "node_modules", ".lake", "vendor")

KERNEL = "score/kernel.rs"
BATCH = "score/batch.rs"

findings = []


def read(rel):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as handle:
        return handle.read()


def config_files():
    """Every file in this repository that can carry a build flag, discovered.

    A `config.toml`/`config` counts only inside a `.cargo/` directory, which is
    the only place cargo reads one; every `Cargo.toml`, `rust-toolchain*` and
    `build.rs` counts wherever it is. Sorted, repo-relative.
    """
    out = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        rel_dir = os.path.relpath(dirpath, ROOT)
        for name in filenames:
            if name not in CONFIG_NAMES:
                continue
            if name in ("config.toml", "config") and \
                    os.path.basename(dirpath) != ".cargo":
                continue
            out.append(os.path.normpath(os.path.join(rel_dir, name)))
    return sorted(out)


def scan_config_text(rel, text):
    """Findings for one build-configuration file.  Injectable, so the
    calibration can plant a flag without writing to the tree."""
    out = []
    for flag, why in FORBIDDEN:
        if flag in text:
            out.append(
                f"{rel}: build flag {flag!r} is present. {why}. The scoring "
                f"kernel's accumulation order and NaN handling are part of "
                f"the specification; see this file's header for the "
                f"assembly-level baseline it would break.")
    return out


def check_configs():
    scanned = config_files()
    # A guard that scanned nothing must not report a clean build configuration.
    # The repository has a root Cargo.toml at minimum; zero means ROOT is wrong,
    # which is the defect that emptied the extraction tier.
    if not scanned:
        findings.append(
            f"NO BUILD CONFIGURATION FOUND under {ROOT}. This guard examined "
            f"nothing, so its silence is not evidence; the repository root it "
            f"computed is wrong.")
    for rel in scanned:
        text = read(rel)
        if text is None:
            continue
        findings.extend(scan_config_text(rel, text))
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


def scan_source_text(rel, text):
    """Findings for one scoring-kernel source file.  Injectable, so the
    calibration can plant a fast-math intrinsic without editing the kernel."""
    return [f"{rel}: uses {token}. {why}."
            for token, why in FORBIDDEN_SOURCE if token in text]


def check_sources():
    for rel in (KERNEL, BATCH):
        text = read(rel)
        if text is None:
            findings.append(f"MISSING: {rel} does not exist; this guard is "
                            f"pinned to a file that moved.")
            continue
        findings.extend(scan_source_text(rel, text))


def check_kernel_shape():
    """The two properties the measured error bound depends on."""
    kernel = read(KERNEL)
    batch = read(BATCH)
    if kernel is None or batch is None:
        return
    findings.extend(scan_kernel_shape(kernel, batch))


def scan_kernel_shape(kernel, batch):
    """Findings for the accumulation shape.  Injectable for the same reason:
    these three checks are pinned to the real kernel and had never been
    observed to fire, which is indistinguishable from being unable to."""
    findings = []

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

    return findings


def workflow_run_paths(text):
    """Repo-relative script paths that prover.yml actually EXECUTES.

    Scoped to `run:` blocks and resolved against the step's `working-directory`,
    because the file is full of prose that names paths it deliberately does NOT
    run -- the "WHAT IS NOT WIRED UP" section lists a dozen of them, and matching
    those would make this guard fire on the very comment explaining why they are
    excluded. Comment lines are dropped for the same reason. Line-based rather
    than YAML-parsed so the guard has no dependency of its own.
    """
    paths, workdir, in_run, run_indent = set(), None, False, 0
    for raw in text.splitlines():
        stripped = raw.strip()
        indent = len(raw) - len(raw.lstrip())

        if in_run and stripped and indent <= run_indent:
            in_run = False
        if stripped.startswith("#"):
            continue
        if re.match(r"-\s+(name|uses):", stripped):
            workdir, in_run = None, False
        m = re.match(r"working-directory:\s*(\S+)", stripped)
        if m:
            workdir = m.group(1).strip("'\"")
            continue
        m = re.match(r"run:\s*(.*)$", stripped)
        if m:
            in_run, run_indent = True, indent
            body = m.group(1).strip()
            if body in ("|", ">", "|-", ">-"):
                body = ""
            _collect(body, workdir, paths)
            continue
        if in_run:
            _collect(stripped, workdir, paths)
    return paths


def _collect(command, workdir, out):
    # `.toml` is included for `cargo --manifest-path`, which is the LAST run:
    # step in prover.yml and therefore the only path that sits after the
    # "WHAT IS NOT WIRED UP" prose block. That placement is deliberate: it gives
    # the CALIB-TAIL probe in test_metamorphic.py a real path at the end of the
    # real file, so a parser that stopped early would be caught rather than
    # merely suspected. It is also a genuine check -- a moved Cargo.toml breaks
    # CI exactly as a moved script does.
    for tok in re.findall(r"[\w./-]+\.(?:py|sh|lean|toml)\b", command):
        if "://" in command and tok in command.split()[-1:]:
            continue                       # curl <url> | sh, not a repo file
        if tok.startswith(("/", "-")) or "//" in tok:
            continue
        out.add(os.path.normpath(os.path.join(workdir, tok)) if workdir else tok)


def check_workflow_paths():
    """Every file prover.yml runs must be TRACKED IN GIT.

    A CI step and the file it runs must land in the same commit.  In this repo
    they can come apart silently, because the git index is shared between
    concurrent sessions: `git add` on prover.yml takes whatever another session
    has left in it, so a commit can pick up a step whose script is still
    untracked.  That happened -- a "Calibrate the identity gate" step rode into
    main across three commits while `test_identity_gate.py` was untracked, and CI
    would have failed on a missing file the whole time.  The break is invisible
    to every checker in this directory, because the corpus is fine; it is the
    pipeline that is broken.

    Anchored to the paths prover.yml actually names, so it needs no list of its
    own to fall out of date.
    """
    wf_rel = os.path.join(".github", "workflows", "prover.yml")
    text = read(wf_rel)
    if text is None:
        findings.append(f"MISSING: {wf_rel}; this guard is pinned to a file "
                        f"that moved.")
        return

    named = workflow_run_paths(text)

    tracked = None
    try:
        import subprocess
        out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT,
                             capture_output=True, timeout=60)
        if out.returncode == 0:
            tracked = set(out.stdout.decode("utf-8").split("\0"))
    except Exception:
        tracked = None

    if tracked is None:
        print("  (workflow-path check skipped: git not available here)")
        return

    for path in sorted(named):
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            findings.append(
                f"{wf_rel} runs {path}, which DOES NOT EXIST. CI on main will "
                f"fail on a missing file. A CI step and the file it runs must "
                f"land in the same commit.")
        elif path not in tracked:
            findings.append(
                f"{wf_rel} runs {path}, which exists locally but is NOT TRACKED "
                f"IN GIT. CI checks out the commit, not your working tree, so "
                f"this step will fail on main. Commit the file together with "
                f"the step that runs it -- `git add` on the shared index takes "
                f"another session's in-flight prover.yml edits with it.")


def main():
    check_configs()
    check_sources()
    check_kernel_shape()
    check_workflow_paths()
    print("build-configuration guard: "
          f"{len(config_files())} build-configuration files discovered "
          f"({', '.join(config_files()[:6])}"
          f"{', ...' if len(config_files()) > 6 else ''}), "
          f"{len(FORBIDDEN)} forbidden flags, "
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
