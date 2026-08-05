#!/usr/bin/env python3
"""Every file a CI step runs must be TRACKED IN GIT.

    python3 validation/code/workflow_paths.py

WHY THIS EXISTS.  A CI step and the file it runs must land in the same commit.
They can come apart silently: `git add` on prover.yml takes whatever another
session has left in it, so a commit can pick up a step whose script is still
untracked.  That happened -- a "Calibrate the identity gate" step rode into
main across three commits while `test_identity_gate.py` was untracked, and CI
would have failed on a missing file the whole time.  The break is invisible to
every other checker here, because the corpus is fine; it is the pipeline that
is broken.

Anchored to the paths prover.yml actually names, so it needs no list of its own
to fall out of date.

PROVENANCE.  This guard was `check_workflow_paths` in
`validation/empirical/metamorphic/build_flags.py`, whose other three
checks scanned the Rust scoring kernel's build configuration for fast-math
flags.  That kernel lives in gnomon, not here, so those checks left with it
when the corpus was split out; this one is repo-generic and stayed.  Its
calibration is `workflow_path_extraction` in
`validation/empirical/metamorphic/test_metamorphic.py`.
"""

import os
import re
import sys

# validation/code/workflow_paths.py, so two levels up is the repository root.
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "..", ".."))

findings = []


def read(rel):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as handle:
        return handle.read()



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
    check_workflow_paths()
    wf_rel = os.path.join(".github", "workflows", "prover.yml")
    text = read(wf_rel)
    named = workflow_run_paths(text) if text else set()
    print(f"workflow-path guard: {len(named)} executed path(s) named by "
          f"{wf_rel}, each checked for existence and for being tracked in git.")
    if findings:
        print(f"\n{len(findings)} FINDING(S):\n")
        for f in findings:
            print("  " + f)
        return 1
    print("every file prover.yml runs is present and tracked.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
