#!/usr/bin/env python3
"""Run a simulation family end to end, and land a result nobody has to
hand-verify.

WHY THIS EXISTS. Hand-verification is the binding constraint on running thirty
families -- not CPU and not memory. Every rule enforced below is here because
this project lost time to the exact failure it prevents, and every one of them
is recorded in the validation README with its instance:

  1.  BOTH STREAMS, CAPTURED SEPARATELY. A 25-second probe harness collected
      stderr only. A family that reports a failed check on STDOUT and exits
      nonzero was recorded as CRASHING. It had run fine. So this harness keeps
      the two streams in two files, and treats the exit code as DATA: a nonzero
      exit is a measurement outcome, never a failure by itself. The only things
      that make THIS script exit nonzero are its own inability to do its job.

  2.  PROVENANCE, OR NO RECORD. Revision, working-tree cleanliness, the dirty
      paths, timestamp, host, interpreter. `simprov.stamp` already writes those
      with the same field names as `Shared.Results.write` on the Lean side, so
      it is used rather than reimplemented. A results file that cannot name the
      revision it describes is a number, not a measurement -- so if the stamp
      cannot name a revision, this script refuses to run at all rather than
      recording an unattributable result.

  3.  DIFF, NEVER OVERWRITE. A stored result is the only cross-check that
      exists, and the case where it is worth most is exactly the case where the
      script that produced it no longer runs. The fresh run goes to a new path
      and is compared. Several families here write to `os.path.join(HERE, ...)`
      and would clobber their own stored result: those writes are detected and
      UNDONE from a pre-run content-addressed snapshot, with the restoration
      verified by hash.

      The comparison reports STRUCTURAL differences (a key in one and not the
      other, a list whose length changed, a type change, a boolean flip)
      SEPARATELY from numeric ones, because they mean different things. For
      numeric it reports the worst absolute difference, the worst relative
      difference, and the count of differing leaves. Two families were
      confirmed this way at worst relative differences of 1.8e-14 and 3.3e-13,
      which is floating-point reduction order rather than disagreement -- a
      distinction that exists only if it is measured instead of eyeballed.

  4.  VERIFY THAT THE WORK HAPPENED. A `sed` that matched nothing exited 0 and
      produced a byte-identical script that would have measured the wrong tree.
      So every transformation here checks its own effect: a copy is re-hashed,
      a restore is re-hashed against the snapshot, and the fresh results file is
      proved to be a DIFFERENT FILE from the baseline before anything is
      compared -- otherwise a family that wrote nothing would have its baseline
      diffed against itself and reported as agreeing perfectly.

  5.  VERDICT FIRST, LOG SECOND. A real guard finding sat unread at the bottom
      of a long advisory list for hours. A finding that is not surfaced is
      functionally invisible. Every summary this writes puts the verdict at the
      top, and SUMMARY.txt is rewritten after EACH family, so a crash on family
      seven still leaves a readable verdict for families one to six.

  6.  THE INTERPRETER IS A PARAMETER. The cluster default `python3` is 3.6.8
      and cannot run modern code; a guard died on a SyntaxError and its nonzero
      exit was indistinguishable from a finding for an entire build. The family
      interpreter is taken as an argument, verified by running it before any
      family is launched, and a bad one is a loud refusal (exit 4) rather than
      a silent fallback.

  7.  NO PATH IS INFERRED BY COUNTING PARENTS. The repository root is the
      directory containing `.git`, found by walking up. The output directory is
      an argument. `parents[2]` survived a directory move by evaluating to a
      real but wrong path, twice in one day, and that is the worst available
      outcome.

WHAT IT WRITES.  Under `--out DIR`:

    SUMMARY.txt              verdict-first, rewritten after every family
    index.jsonl              one summary object per line, appended and flushed
    _vault/<sha256>          content-addressed snapshots of clobbered baselines
    <family>/summary.json    the harness summary object for that family
    <family>/stdout.txt      the family's stdout, complete
    <family>/stderr.txt      the family's stderr, complete
    <family>/<name>.json     the family's OWN results file, relocated here

The family's own results file keeps the schema the family already emits. This
script imposes nothing on it; it only reads `READ_THE_TEST` and `failed_checks`
if they happen to be there, because the families that have them are the ones
whose verdict is worth surfacing.

KEPT TO PYTHON 3.6. This runs on the cluster, and pinning the FAMILY
interpreter is no help if the pin itself will not parse under the ambient one.
No f-strings with `=`, no walrus, no `from __future__ import annotations`, no
`subprocess.run(capture_output=)`, no dataclasses.
"""

import argparse
import errno
import hashlib
import json
import math
import os
import re
import shlex
import shutil
import subprocess
import sys
import time


# ---------------------------------------------------------------------------
# Locating things. Nothing here counts parent directories.
# ---------------------------------------------------------------------------

HARNESS_VERSION = 1

# Exit codes. Only the harness's own inability to work is nonzero by default;
# a family's nonzero exit is data. See `--fail-on-diff` for the opt-in.
EXIT_OK = 0
EXIT_DIFFERENCES = 3      # only with --fail-on-diff
EXIT_NO_INTERPRETER = 4   # same code the cluster build script uses, same reason
EXIT_HARNESS_ERROR = 5


def find_repo_root(start):
    """The repository root: the directory that contains `.git`.

    Not `parents[2]`, and not four `..` segments. Both of those have already
    converted a directory move in this repository into a plausible wrong answer
    rather than an error -- once in the provenance module, where it silently
    added 83 unrelated files to the dirty-path list, and once in a family, where
    it pointed the study data at a directory that has never existed.
    """
    here = os.path.abspath(start)
    if os.path.isfile(here):
        here = os.path.dirname(here)
    while True:
        if os.path.exists(os.path.join(here, ".git")):
            return here
        parent = os.path.dirname(here)
        if parent == here:
            return None
        here = parent


def import_simprov(repo_root, explicit):
    """Import the provenance module, or say exactly which path was tried.

    Four scripts in this directory bootstrap `simprov` with a fixed number of
    `dirname()` calls and survive only because they and `simprov.py` moved
    together. This asks for the thing it wants: the repository root, then the
    module's tracked location under it, and it accepts an override so a caller
    who has moved it can say so instead of being guessed at.
    """
    cands = []
    if explicit:
        cands.append(os.path.abspath(explicit))
    if repo_root:
        cands.append(os.path.join(
            repo_root, "validation", "empirical", "simprov.py"))
    for path in cands:
        if os.path.isfile(path):
            d = os.path.dirname(path)
            if d not in sys.path:
                sys.path.insert(0, d)
            import simprov  # noqa: F401
            return simprov, path
    raise SystemExit(
        "harness: cannot import simprov; tried:\n  " + "\n  ".join(cands or
        ["(no repository root found, and no --simprov given)"]) +
        "\nA result without a provenance stamp is a number, not a measurement,"
        "\nso this refuses to run rather than recording one. Pass --simprov"
        " PATH.")


# ---------------------------------------------------------------------------
# Hashing, and the content-addressed vault that makes "never overwrite" true
# even for families that write in place.
# ---------------------------------------------------------------------------

def sha256_file(path):
    h = hashlib.sha256()
    fh = open(path, "rb")
    try:
        while True:
            chunk = fh.read(1 << 20)
            if not chunk:
                break
            h.update(chunk)
    finally:
        fh.close()
    return h.hexdigest()


def file_stat(path):
    """Identity and content of a file, or None if it is not there."""
    if not os.path.isfile(path):
        return None
    st = os.stat(path)
    return {"path": os.path.abspath(path), "bytes": st.st_size,
            "mtime": st.st_mtime, "sha256": sha256_file(path),
            "dev": st.st_dev, "ino": st.st_ino}


class Vault(object):
    """Content-addressed snapshots, so a clobbered baseline can be put back.

    Keyed by hash, so thirty families that each snapshot the same twenty
    unchanged JSON files store them once.
    """

    def __init__(self, root):
        self.root = root
        makedirs(root)

    def stash(self, path):
        digest = sha256_file(path)
        blob = os.path.join(self.root, digest)
        if not os.path.exists(blob):
            shutil.copyfile(path, blob)
            # Rule 4: a copy that silently did nothing is the whole failure
            # mode this project keeps hitting. Prove the bytes arrived.
            got = sha256_file(blob)
            if got != digest:
                raise HarnessError(
                    "vault: snapshot of %s hashed %s but stored %s"
                    % (path, digest, got))
        return digest

    def restore(self, digest, path):
        blob = os.path.join(self.root, digest)
        if not os.path.isfile(blob):
            raise HarnessError("vault: no snapshot %s to restore to %s"
                               % (digest, path))
        shutil.copyfile(blob, path)
        got = sha256_file(path)
        if got != digest:
            raise HarnessError(
                "vault: restored %s but it hashed %s, wanted %s"
                % (path, got, digest))
        return True


class HarnessError(Exception):
    pass


def makedirs(path):
    try:
        os.makedirs(path)
    except OSError as exc:
        if exc.errno != errno.EEXIST:
            raise


def copy_verified(src, dst):
    """Copy, then prove the copy happened and matches.

    `shutil.copyfile` will not silently no-op the way `sed` did, but the point
    of rule 4 is that the check is cheap and the failure it catches is one this
    project has already paid for once.
    """
    want = sha256_file(src)
    shutil.copyfile(src, dst)
    got = sha256_file(dst)
    if got != want:
        raise HarnessError("copy %s -> %s: hashed %s, wanted %s"
                           % (src, dst, got, want))
    return want


# ---------------------------------------------------------------------------
# The comparison. This is the part most likely to be quietly wrong, so it is a
# pure function over parsed JSON with no I/O, and it is unit tested.
# ---------------------------------------------------------------------------

DEFAULT_IGNORE = [
    "$._provenance",   # revision, host, timestamp: differ by construction
    "$.runtime_sec",   # wall clock is not a measurement of the model
    "$.runtime",
    "$.duration_sec",
    "$.elapsed_sec",
    "$.argv",
]

DEFAULT_RTOL = 1e-9
DEFAULT_ATOL = 0.0


def kind_of(value):
    """The type as the diff cares about it.

    `bool` is separated from `number` deliberately. In Python `True == 1`, so a
    naive numeric comparison would let `READ_THE_TEST` flip from true to false
    and report it as a numeric difference of 1.0 buried among the floats. A
    boolean flip is structural: it is the family changing its verdict.
    """
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "bool"
    if isinstance(value, (int, float)):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "list"
    if isinstance(value, dict):
        return "dict"
    return "other"


def render_path(parts):
    out = "$"
    for p in parts:
        if isinstance(p, int):
            out += "[%d]" % p
        else:
            out += "." + str(p)
    return out


_PATTERN_CACHE = {}


def _pattern_regex(pat):
    """Compile an ignore pattern.

    `[*]` means ANY LIST INDEX, which is what someone writing
    `$.C1.cells[*].se` means. Plain `fnmatch` would read `[*]` as a character
    class containing an asterisk and match only a literal `[*]` -- a pattern
    that silently matches nothing is exactly the `sed` failure in another
    costume, so the bracket form is translated explicitly.
    """
    if pat in _PATTERN_CACHE:
        return _PATTERN_CACHE[pat]
    out, i = [], 0
    while i < len(pat):
        if pat.startswith("[*]", i):
            out.append(r"\[[0-9]+\]")
            i += 3
        elif pat[i] == "*":
            out.append(".*")
            i += 1
        else:
            out.append(re.escape(pat[i]))
            i += 1
    rx = re.compile("".join(out) + r"$")
    _PATTERN_CACHE[pat] = rx
    return rx


def path_ignored(path_str, patterns):
    """The pattern that excludes this path, or None.

    A pattern matches the path itself, any descendant of it, or a glob.
    Returns the pattern rather than a bare True so the summary can say WHICH
    rule dropped a path: an exclusion nobody can trace is how a real
    difference disappears.
    """
    for pat in patterns:
        if path_str == pat:
            return pat
        if path_str.startswith(pat + ".") or path_str.startswith(pat + "["):
            return pat
        if _pattern_regex(pat).match(path_str):
            return pat
    return None


def _abbrev(value, limit=200):
    try:
        text = json.dumps(value, default=repr)
    except Exception:
        text = repr(value)
    if len(text) > limit:
        text = text[:limit] + "...<%d chars>" % len(text)
    return text


def compare_json(stored, fresh, ignore=None, rtol=DEFAULT_RTOL,
                 atol=DEFAULT_ATOL, max_examples=50):
    """Compare two decoded JSON documents.

    Returns a dict with STRUCTURAL and NUMERIC differences in separate lists,
    because they mean different things. A structural difference means the two
    runs are not the same measurement. A numeric difference within tolerance
    means they are the same measurement summed in a different order.

    Non-finite mismatches (a NaN where there was a number, an infinity where
    there was a finite value) are reported as STRUCTURAL, not numeric: the
    relative difference is undefined, and quietly dropping them would hide a
    cell whose replicates started failing.
    """
    patterns = list(DEFAULT_IGNORE if ignore is None else ignore)
    state = {
        "structural": [],
        "numeric": [],
        "ignored": [],
        "leaves_compared": 0,
        "leaves_equal": 0,
    }

    def add_struct(parts, reason, stored_v, fresh_v, extra=None):
        item = {"path": render_path(parts), "reason": reason,
                "stored": _abbrev(stored_v), "fresh": _abbrev(fresh_v)}
        if extra:
            item.update(extra)
        state["structural"].append(item)

    def walk(parts, a, b):
        path_str = render_path(parts)
        hit = path_ignored(path_str, patterns)
        if hit is not None:
            state["ignored"].append({"path": path_str, "pattern": hit})
            return

        ka, kb = kind_of(a), kind_of(b)
        if ka != kb:
            add_struct(parts, "type changed", a, b,
                       {"stored_kind": ka, "fresh_kind": kb})
            return

        if ka == "dict":
            akeys, bkeys = set(a.keys()), set(b.keys())
            for k in sorted(akeys - bkeys):
                add_struct(parts + [k], "key missing from fresh", a[k], None)
            for k in sorted(bkeys - akeys):
                add_struct(parts + [k], "key added in fresh", None, b[k])
            for k in sorted(akeys & bkeys):
                walk(parts + [k], a[k], b[k])
            return

        if ka == "list":
            if len(a) != len(b):
                add_struct(parts, "list length changed", len(a), len(b),
                           {"stored_len": len(a), "fresh_len": len(b)})
            # Recurse over the common prefix anyway. A length change must not
            # hide the fact that the elements that DO exist in both also moved.
            for i in range(min(len(a), len(b))):
                walk(parts + [i], a[i], b[i])
            return

        state["leaves_compared"] += 1

        if ka == "null":
            state["leaves_equal"] += 1
            return

        if ka == "bool":
            if a is b or a == b:
                state["leaves_equal"] += 1
            else:
                add_struct(parts, "boolean flipped", a, b)
            return

        if ka == "string":
            if a == b:
                state["leaves_equal"] += 1
            else:
                add_struct(parts, "string changed", a, b)
            return

        if ka == "number":
            fa, fb = float(a), float(b)
            na, nb = math.isnan(fa), math.isnan(fb)
            if na and nb:
                state["leaves_equal"] += 1
                return
            if na or nb:
                add_struct(parts, "nan mismatch", a, b)
                return
            ia, ib = math.isinf(fa), math.isinf(fb)
            if ia or ib:
                if ia and ib and fa == fb:
                    state["leaves_equal"] += 1
                else:
                    add_struct(parts, "infinity mismatch", a, b)
                return
            if fa == fb:
                state["leaves_equal"] += 1
                return
            adiff = abs(fa - fb)
            scale = max(abs(fa), abs(fb))
            rdiff = adiff / scale if scale > 0.0 else 0.0
            state["numeric"].append({
                "path": path_str, "stored": fa, "fresh": fb,
                "abs": adiff, "rel": rdiff,
                "within_tolerance": bool(adiff <= atol or rdiff <= rtol),
            })
            return

        # kind_of returned "other": a decoder produced something json cannot
        # have produced. Say so rather than guessing.
        if a == b:
            state["leaves_equal"] += 1
        else:
            add_struct(parts, "unhandled value changed", a, b)

    walk([], stored, fresh)

    nums = state["numeric"]
    beyond = [n for n in nums if not n["within_tolerance"]]
    worst_abs = max(nums, key=lambda n: n["abs"]) if nums else None
    worst_rel = max(nums, key=lambda n: n["rel"]) if nums else None

    return {
        "tolerance": {"rtol": rtol, "atol": atol},
        "ignored_patterns": patterns,
        "ignored_paths": state["ignored"][:max_examples],
        "ignored_count": len(state["ignored"]),
        "leaves_compared": state["leaves_compared"],
        "leaves_equal": state["leaves_equal"],
        "structural_count": len(state["structural"]),
        "structural": state["structural"][:max_examples],
        "structural_truncated": max(0, len(state["structural"]) - max_examples),
        "numeric_differing_count": len(nums),
        "numeric_beyond_tolerance_count": len(beyond),
        "numeric_worst_abs": worst_abs,
        "numeric_worst_rel": worst_rel,
        "numeric_beyond_tolerance": beyond[:max_examples],
        "numeric_beyond_truncated": max(0, len(beyond) - max_examples),
        "identical": (len(state["structural"]) == 0 and len(nums) == 0),
        "agrees_within_tolerance": (len(state["structural"]) == 0
                                    and len(beyond) == 0),
    }


def diff_verdict(diff):
    """The one word that goes at the top. Structural dominates numeric."""
    if diff["structural_count"] > 0:
        return "STRUCTURAL_DIFFERENCE"
    if diff["numeric_beyond_tolerance_count"] > 0:
        return "NUMERIC_DIFFERENCE"
    if diff["numeric_differing_count"] > 0:
        return "AGREES_TO_FLOATING_POINT"
    return "IDENTICAL"


def diff_headline(diff):
    """One line of detail to sit beside the verdict word."""
    if diff["structural_count"]:
        first = diff["structural"][0]
        return ("%d structural (%s at %s), %d numeric beyond tol"
                % (diff["structural_count"], first["reason"], first["path"],
                   diff["numeric_beyond_tolerance_count"]))
    if diff["numeric_beyond_tolerance_count"]:
        w = diff["numeric_worst_rel"]
        return ("%d of %d numeric leaves beyond tol; worst rel %.3g at %s"
                % (diff["numeric_beyond_tolerance_count"],
                   diff["leaves_compared"], w["rel"], w["path"]))
    if diff["numeric_differing_count"]:
        w = diff["numeric_worst_rel"]
        wa = diff["numeric_worst_abs"]
        return ("%d of %d leaves differ; worst rel %.3g at %s, worst abs %.3g "
                "at %s -- reduction order, not disagreement"
                % (diff["numeric_differing_count"], diff["leaves_compared"],
                   w["rel"], w["path"], wa["abs"], wa["path"]))
    return "%d leaves, byte-for-byte agreement" % diff["leaves_compared"]


# ---------------------------------------------------------------------------
# The interpreter. Pinned, verified, and never fallen back from.
# ---------------------------------------------------------------------------

PROBE = ("import sys, json, platform;"
         "print(json.dumps({'version': sys.version.split()[0],"
         "'version_info': list(sys.version_info[:3]),"
         "'executable': sys.executable, 'impl': platform.python_implementation()}))")


def verify_interpreter(spec, min_version, require_imports):
    """Run the interpreter and make it say what it is, before anything else.

    A guard died on a SyntaxError under the cluster's 3.6.8 default and its
    nonzero exit read as a finding for an entire build. The fix is not to guess
    better; it is to make the interpreter prove itself, once, loudly, before a
    single family starts -- and to refuse rather than fall back, because a
    fallback is how the wrong interpreter gets used in the first place.
    """
    resolved = spec if os.path.sep in spec else shutil.which(spec)
    info = {"requested": spec, "resolved": resolved, "usable": False,
            "min_version": list(min_version), "required_imports": list(require_imports)}
    if not resolved or not os.path.exists(resolved):
        info["problem"] = "not found on PATH and not an existing file"
        return info
    if not os.access(resolved, os.X_OK):
        info["problem"] = "exists but is not executable"
        return info
    try:
        proc = subprocess.Popen([resolved, "-c", PROBE],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
    except Exception as exc:
        info["problem"] = "could not be executed: %s" % exc
        return info
    if proc.returncode != 0:
        info["problem"] = ("exited %d on a trivial probe; stderr: %s"
                           % (proc.returncode,
                              err.decode("utf-8", "replace").strip()[:400]))
        return info
    try:
        info.update(json.loads(out.decode("utf-8", "replace")))
    except Exception as exc:
        info["problem"] = "probe output was not JSON: %s" % exc
        return info
    if tuple(info["version_info"]) < tuple(min_version):
        info["problem"] = ("is %s, below the required %s. The cluster default "
                           "python3 is 3.6.8 and cannot run modern code; that "
                           "is why this is checked rather than assumed."
                           % (info["version"],
                              ".".join(str(v) for v in min_version)))
        return info
    missing = []
    for mod in require_imports:
        p = subprocess.Popen([resolved, "-c", "import " + mod],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        p.communicate()
        if p.returncode != 0:
            missing.append(mod)
    if missing:
        info["problem"] = "cannot import: " + ", ".join(missing)
        info["missing_imports"] = missing
        return info
    info["usable"] = True
    return info


# ---------------------------------------------------------------------------
# Running one family.
# ---------------------------------------------------------------------------

def family_stem(script):
    return os.path.splitext(os.path.basename(script))[0]


def snapshot_dir_json(directory, vault):
    """Hash every JSON file beside the family, and vault its contents.

    Several families write their results to `os.path.join(HERE, ...)` and would
    overwrite the stored result this harness exists to compare against. Their
    scripts are not being edited from here, so instead: record what was there,
    and put it back afterwards.
    """
    snap = {}
    for name in sorted(os.listdir(directory)):
        if not name.endswith(".json"):
            continue
        path = os.path.join(directory, name)
        if not os.path.isfile(path):
            continue
        snap[name] = {"sha256": vault.stash(path),
                      "bytes": os.path.getsize(path)}
    return snap


def read_text(path):
    if not os.path.isfile(path):
        return ""
    fh = open(path, "rb")
    try:
        return fh.read().decode("utf-8", "replace")
    finally:
        fh.close()


def launch(argv, stdout_path, stderr_path, cwd, timeout):
    """Run the family, with the two streams going to two separate files.

    THE POINT OF THE TWO FILES. A probe harness collected stderr only, and a
    family that reports a failed check on STDOUT and exits nonzero by design
    was recorded as CRASHING. It had run fine. Both streams are captured, they
    stay separable because they are separate files, and the return code comes
    back as a value for the caller to record rather than to react to.
    """
    fo = open(stdout_path, "wb")
    fe = open(stderr_path, "wb")
    timed_out = False
    launch_error = None
    rc = None
    try:
        try:
            proc = subprocess.Popen(argv, stdout=fo, stderr=fe, cwd=cwd)
        except Exception as exc:
            return {"returncode": None, "timed_out": False,
                    "launch_error": "%s: %s" % (type(exc).__name__, exc)}
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            rc = proc.wait()
    finally:
        fo.close()
        fe.close()
    return {"returncode": rc, "timed_out": timed_out,
            "launch_error": launch_error}


def tail_lines(path, n):
    if not os.path.isfile(path):
        return []
    fh = open(path, "rb")
    try:
        data = fh.read()
    finally:
        fh.close()
    text = data.decode("utf-8", "replace")
    lines = text.splitlines()
    return lines[-n:]


_OUTPUT_ARG = re.compile(r"""add_argument\(\s*["']--output["']""")

UNRECOGNIZED = "unrecognized arguments"


def supports_output_flag(script):
    """Does the family register an `--output` flag? Read its source; do not
    run it.

    Of the families in this directory only some take the flag, and the set will
    change, so a hardcoded list would rot. The first version of this asked the
    family by running `<script> --help` -- which for a family with no argparse
    at all does not print help, it RUNS THE WHOLE SIMULATION. A probe that
    silently costs a second full run of an hours-long family is not a probe.

    Matching the argparse registration rather than the bare string means a
    mention in a docstring or a comment does not produce a false positive. A
    false positive here is not silent either: the family exits 2 with
    'unrecognized arguments' and `run_family` retries once without the flag.
    """
    try:
        fh = open(script, "r")
        try:
            text = fh.read()
        finally:
            fh.close()
    except Exception as exc:
        return False, "could not read the script to look for --output: %s" % exc
    if _OUTPUT_ARG.search(text):
        return True, "the script registers --output; the fresh path is passed"
    return False, ("the script registers no --output; it will run with its "
                   "working directory set to the run directory, and anything "
                   "it writes beside itself is relocated afterwards")


def run_family(script, extra_args, opts, vault, out_root):
    """Run one family and return its summary object. Never raises for a
    family-side problem: a crash, a timeout and a failed check are all
    outcomes, and all three are recorded."""
    script = os.path.abspath(script)
    stem = family_stem(script)
    run_dir = os.path.join(out_root, stem)
    makedirs(run_dir)

    script_dir = os.path.dirname(script)
    notes = []

    summary = {
        "harness_version": HARNESS_VERSION,
        "verdict": "PENDING",
        "verdict_detail": "",
        "family": {"script": script, "stem": stem,
                   "exists": os.path.isfile(script)},
        "run_dir": run_dir,
        "interpreter": opts["interpreter_info"],
        "notes": notes,
    }

    if not os.path.isfile(script):
        summary["verdict"] = "MISSING_FAMILY"
        summary["verdict_detail"] = "no such file: " + script
        return summary

    baseline_path = opts["baseline"]
    if baseline_path is None:
        guess = os.path.join(script_dir, stem + "_results.json")
        baseline_path = guess if os.path.isfile(guess) else None
    baseline_before = file_stat(baseline_path) if baseline_path else None

    # Everything in the family's own directory that could be clobbered.
    pre_snapshot = snapshot_dir_json(script_dir, vault)

    takes_output, output_reason = supports_output_flag(script)
    notes.append("output flag: " + output_reason)

    fresh_target = os.path.join(run_dir, stem + "_results.json")
    base_argv = [opts["python"], script] + list(extra_args)
    argv = base_argv + (["--output", fresh_target] if takes_output else [])

    stdout_path = os.path.join(run_dir, "stdout.txt")
    stderr_path = os.path.join(run_dir, "stderr.txt")

    t0 = time.time()
    started_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    run = launch(argv, stdout_path, stderr_path, run_dir, opts["timeout"])

    # If the static scan was wrong about `--output`, argparse says so and exits
    # 2 without running anything. Retry once, without the flag, rather than
    # recording a family as having produced no results when it never started.
    if takes_output and run["returncode"] not in (0, None):
        err = read_text(stderr_path)
        if UNRECOGNIZED in err and "--output" in err:
            # Keep the rejected attempt: a re-run must not erase the evidence
            # that explains why it happened.
            for name in ("stdout.txt", "stderr.txt"):
                os.rename(os.path.join(run_dir, name),
                          os.path.join(run_dir, name + ".rejected-output-flag"))
            notes.append("the script matched the --output registration but "
                         "rejected the flag; re-ran once without it. The "
                         "rejected attempt's streams are kept alongside as "
                         "*.rejected-output-flag")
            argv = base_argv
            takes_output = False
            run = launch(argv, stdout_path, stderr_path, run_dir,
                         opts["timeout"])

    elapsed = time.time() - t0
    summary["invocation"] = {
        "argv": argv, "cwd": run_dir, "started_at": started_at,
        "duration_sec": elapsed, "timeout_sec": opts["timeout"],
        "timed_out": run["timed_out"], "launch_error": run["launch_error"],
        "passed_output_flag": takes_output,
    }
    rc = run["returncode"]
    timed_out = run["timed_out"]
    # THE EXIT CODE IS DATA. It is recorded, described, and never on its own
    # treated as a failure: for several families here a nonzero exit means a
    # check failed and the full report went to stdout.
    summary["exit"] = {
        "code": rc,
        "signal": (-rc if (rc is not None and rc < 0) else None),
        "meaning": ("recorded as a measurement outcome; a nonzero exit from a "
                    "family means a check failed, not that the run crashed"),
    }
    summary["streams"] = {
        "stdout_path": stdout_path,
        "stdout_bytes": os.path.getsize(stdout_path),
        "stdout_tail": tail_lines(stdout_path, opts["tail"]),
        "stderr_path": stderr_path,
        "stderr_bytes": os.path.getsize(stderr_path),
        "stderr_tail": tail_lines(stderr_path, opts["tail"]),
    }

    # --- What did it write, and where? -------------------------------------
    post = {}
    for name in sorted(os.listdir(script_dir)):
        if name.endswith(".json") and os.path.isfile(
                os.path.join(script_dir, name)):
            post[name] = sha256_file(os.path.join(script_dir, name))

    clobbered = []
    for name, rec in sorted(pre_snapshot.items()):
        now = post.get(name)
        if now is None:
            notes.append("baseline %s disappeared during the run" % name)
            continue
        if now != rec["sha256"]:
            clobbered.append(name)
    created_in_place = sorted(set(post) - set(pre_snapshot))

    in_place = []
    for name in clobbered + created_in_place:
        src = os.path.join(script_dir, name)
        dst = os.path.join(run_dir, name)
        try:
            copy_verified(src, dst)
        except HarnessError as exc:
            notes.append("could not relocate in-place write %s: %s"
                         % (name, exc))
            continue
        in_place.append({"name": name, "relocated_to": dst,
                         "was_existing": name in pre_snapshot})
        if name in pre_snapshot:
            # Rule 3, made true rather than merely intended: put the stored
            # result back, from the pre-run snapshot, and verify by hash.
            vault.restore(pre_snapshot[name]["sha256"], src)
            notes.append("family wrote %s IN PLACE over the stored result; "
                         "the fresh copy is at %s and the stored file was "
                         "restored from a pre-run snapshot and hash-verified"
                         % (name, dst))
        else:
            os.remove(src)
            notes.append("family created %s beside its script; moved to %s so "
                         "the tracked directory is left as it was" % (name, dst))

    summary["in_place_writes"] = in_place

    # The family's own results file, wherever it ended up.
    candidates = []
    if os.path.isfile(fresh_target):
        candidates.append(fresh_target)
    for entry in in_place:
        if entry["relocated_to"] not in candidates:
            candidates.append(entry["relocated_to"])
    for name in sorted(os.listdir(run_dir)):
        p = os.path.join(run_dir, name)
        if (name.endswith(".json") and name != "summary.json"
                and os.path.isfile(p) and p not in candidates):
            candidates.append(p)

    preferred = None
    for p in candidates:
        if os.path.basename(p) == stem + "_results.json":
            preferred = p
            break
    if preferred is None and candidates:
        preferred = candidates[0]

    summary["results"] = {
        "fresh_path": preferred,
        "all_candidates": candidates,
        "baseline_path": baseline_path,
        "baseline_before": baseline_before,
    }

    if preferred is None:
        summary["verdict"] = "NO_RESULTS"
        summary["verdict_detail"] = (
            "the family produced no results file (exit %s%s)"
            % (rc, ", timed out" if timed_out else ""))
        return summary

    fresh_stat = file_stat(preferred)
    summary["results"]["fresh"] = fresh_stat

    # Rule 4, the sharpest instance: if the family wrote nothing and the
    # harness quietly picked up the baseline, the diff would compare a file
    # with itself and report perfect agreement. Prove they are different files.
    if baseline_before is not None:
        same_file = (fresh_stat["dev"] == baseline_before["dev"]
                     and fresh_stat["ino"] == baseline_before["ino"])
        if same_file or os.path.realpath(preferred) == os.path.realpath(
                baseline_before["path"]):
            summary["verdict"] = "HARNESS_ERROR"
            summary["verdict_detail"] = (
                "the fresh results path and the baseline are the SAME FILE "
                "(%s); comparing it with itself would report agreement that "
                "was never measured" % preferred)
            return summary
    if fresh_stat["mtime"] + 1.0 < t0:
        notes.append("the fresh results file predates the run by %.1f s; it "
                     "may be a leftover rather than this run's output"
                     % (t0 - fresh_stat["mtime"]))

    try:
        fresh_doc = json.loads(open(preferred).read())
    except Exception as exc:
        summary["verdict"] = "UNREADABLE_RESULTS"
        summary["verdict_detail"] = "%s is not readable JSON: %s" % (
            preferred, exc)
        return summary

    summary["family_verdict"] = {
        "READ_THE_TEST": (fresh_doc.get("READ_THE_TEST")
                          if isinstance(fresh_doc, dict) else None),
        "failed_checks": (fresh_doc.get("failed_checks")
                          if isinstance(fresh_doc, dict) else None),
    }
    if isinstance(fresh_doc, dict) and isinstance(
            fresh_doc.get("_provenance"), dict):
        prov = fresh_doc["_provenance"]
        summary["results"]["fresh_revision"] = prov.get("revision")
        summary["results"]["fresh_run_at"] = prov.get("runAt")
    else:
        notes.append("the family's results file carries no _provenance block; "
                     "it cannot name the revision it describes")

    if baseline_path is None or baseline_before is None:
        summary["diff"] = None
        summary["verdict"] = "NO_BASELINE"
        summary["verdict_detail"] = (
            "fresh result recorded at %s; there is no stored result to compare "
            "against, so this run becomes the baseline for the next one"
            % preferred)
        return summary

    try:
        stored_doc = json.loads(open(baseline_before["path"]).read())
    except Exception as exc:
        summary["diff"] = None
        summary["verdict"] = "UNREADABLE_BASELINE"
        summary["verdict_detail"] = "%s is not readable JSON: %s" % (
            baseline_before["path"], exc)
        return summary

    if isinstance(stored_doc, dict) and isinstance(
            stored_doc.get("_provenance"), dict):
        prov = stored_doc["_provenance"]
        summary["results"]["baseline_revision"] = prov.get("revision")
        summary["results"]["baseline_run_at"] = prov.get("runAt")
    else:
        notes.append("the STORED result carries no _provenance block, so a "
                     "disagreement here cannot name the revision it is "
                     "against")

    diff = compare_json(stored_doc, fresh_doc, ignore=opts["ignore"],
                        rtol=opts["rtol"], atol=opts["atol"],
                        max_examples=opts["max_examples"])
    summary["diff"] = diff
    summary["verdict"] = diff_verdict(diff)
    summary["verdict_detail"] = diff_headline(diff)

    # Confirm the baseline is byte-identical to what it was before the run.
    # This is the whole "never overwrite" promise, checked rather than assumed.
    after = file_stat(baseline_before["path"])
    summary["results"]["baseline_after"] = after
    summary["results"]["baseline_preserved"] = bool(
        after and after["sha256"] == baseline_before["sha256"])
    if not summary["results"]["baseline_preserved"]:
        notes.append("THE STORED RESULT WAS NOT PRESERVED: %s hashed %s before "
                     "the run and %s after. The only cross-check that exists "
                     "has been damaged; restore it before trusting anything "
                     "here." % (baseline_before["path"],
                                baseline_before["sha256"][:12],
                                (after or {}).get("sha256", "<missing>")))
        summary["verdict"] = "HARNESS_ERROR"
        summary["verdict_detail"] = "the stored result was modified by this run"

    return summary


# ---------------------------------------------------------------------------
# Reporting. Verdict first, every time.
# ---------------------------------------------------------------------------

VERDICT_ORDER = {
    "HARNESS_ERROR": 0,
    "MISSING_FAMILY": 1,
    "UNREADABLE_BASELINE": 2,
    "UNREADABLE_RESULTS": 3,
    "NO_RESULTS": 4,
    "STRUCTURAL_DIFFERENCE": 5,
    "NUMERIC_DIFFERENCE": 6,
    "NO_BASELINE": 7,
    "AGREES_TO_FLOATING_POINT": 8,
    "IDENTICAL": 9,
}

ALARMING = ("HARNESS_ERROR", "MISSING_FAMILY", "UNREADABLE_BASELINE",
            "UNREADABLE_RESULTS", "NO_RESULTS", "STRUCTURAL_DIFFERENCE",
            "NUMERIC_DIFFERENCE")


def summary_line(s):
    fam = s["family"]["stem"]
    rc = s.get("exit", {}).get("code")
    rt = s.get("family_verdict", {}).get("READ_THE_TEST")
    bits = []
    if rc is not None:
        bits.append("exit %s" % rc)
    if rt is not None:
        bits.append("READ_THE_TEST=%s" % rt)
    tag = ("  [%s]" % ", ".join(bits)) if bits else ""
    return "  %-26s %-22s %s%s" % (s["verdict"], fam,
                                   s.get("verdict_detail", ""), tag)


def write_summary_text(path, stamp, summaries, opts):
    """Rewritten after EVERY family, so a crash still leaves a verdict."""
    lines = []
    lines.append("=" * 78)
    lines.append("VERDICT")
    lines.append("=" * 78)
    ordered = sorted(summaries,
                     key=lambda s: VERDICT_ORDER.get(s["verdict"], 99))
    alarming = [s for s in ordered if s["verdict"] in ALARMING]
    if not summaries:
        lines.append("  no families have completed yet")
    elif alarming:
        lines.append("  %d of %d families NEED READING:"
                     % (len(alarming), len(summaries)))
    else:
        lines.append("  %d families run, none needs reading" % len(summaries))
    for s in ordered:
        lines.append(summary_line(s))
    lines.append("")
    lines.append("  A family's nonzero exit is a MEASUREMENT OUTCOME and is "
                 "recorded above as data.")
    lines.append("  It never on its own makes a verdict alarming.")
    lines.append("")
    lines.append("-" * 78)
    lines.append("PROVENANCE")
    lines.append("-" * 78)
    lines.append("  revision   %s%s" % (
        stamp.get("revision"),
        "" if stamp.get("workingTreeClean") else
        "   TREE DIRTY (%d paths)" % len(stamp.get("workingTreeDirtyPaths")
                                          or [])))
    lines.append("  run at     %s on %s" % (stamp.get("runAt"),
                                            stamp.get("host")))
    lines.append("  harness py %s" % stamp.get("python"))
    lines.append("  family py  %s (%s)" % (
        opts["interpreter_info"].get("version"),
        opts["interpreter_info"].get("resolved")))
    lines.append("  tolerance  rtol=%g atol=%g" % (opts["rtol"], opts["atol"]))
    lines.append("")
    lines.append("-" * 78)
    lines.append("DETAIL")
    lines.append("-" * 78)
    for s in ordered:
        lines.append("")
        lines.append("  %s  --  %s" % (s["family"]["stem"], s["verdict"]))
        lines.append("    %s" % s.get("verdict_detail", ""))
        inv = s.get("invocation")
        if inv:
            lines.append("    argv: %s" % " ".join(inv["argv"]))
            lines.append("    %.1f s%s" % (inv["duration_sec"],
                                           ", TIMED OUT" if inv["timed_out"]
                                           else ""))
        res = s.get("results") or {}
        if res.get("fresh_path"):
            lines.append("    fresh    %s" % res["fresh_path"])
        if res.get("baseline_path"):
            lines.append("    stored   %s (preserved: %s)"
                         % (res["baseline_path"],
                            res.get("baseline_preserved")))
            lines.append("    revisions stored=%s fresh=%s"
                         % (str(res.get("baseline_revision"))[:12],
                            str(res.get("fresh_revision"))[:12]))
        d = s.get("diff")
        if d:
            lines.append("    structural %d, numeric differing %d, beyond tol %d,"
                         " leaves compared %d"
                         % (d["structural_count"], d["numeric_differing_count"],
                            d["numeric_beyond_tolerance_count"],
                            d["leaves_compared"]))
            for item in d["structural"][:10]:
                lines.append("      STRUCT %s: %s  stored=%s fresh=%s"
                             % (item["path"], item["reason"], item["stored"],
                                item["fresh"]))
            if d["structural_truncated"]:
                lines.append("      ... and %d more structural"
                             % d["structural_truncated"])
            for item in d["numeric_beyond_tolerance"][:10]:
                lines.append("      NUMER %s: stored=%r fresh=%r abs=%.3g rel=%.3g"
                             % (item["path"], item["stored"], item["fresh"],
                                item["abs"], item["rel"]))
            if d["numeric_beyond_truncated"]:
                lines.append("      ... and %d more beyond tolerance"
                             % d["numeric_beyond_truncated"])
        for n in s.get("notes", []):
            lines.append("    note: %s" % n)
        st = s.get("streams")
        if st:
            lines.append("    stdout %s (%d bytes), stderr %s (%d bytes)"
                         % (st["stdout_path"], st["stdout_bytes"],
                            st["stderr_path"], st["stderr_bytes"]))
            for ln in st["stderr_tail"][-5:]:
                lines.append("      stderr| %s" % ln)
    text = "\n".join(lines) + "\n"
    fh = open(path, "w")
    try:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    finally:
        fh.close()
    return text


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def read_manifest(path):
    """One family per line: `script.py --profile full`. `#` comments, blanks
    skipped. Split with shlex so quoting works the way the shell taught."""
    jobs = []
    fh = open(path)
    try:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = shlex.split(line)
            jobs.append((parts[0], parts[1:]))
    finally:
        fh.close()
    if not jobs:
        raise SystemExit("harness: manifest %s named no families" % path)
    return jobs


def build_parser():
    p = argparse.ArgumentParser(
        prog="harness.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("families", nargs="*", metavar="FAMILY",
                   help="one or more family scripts, run in sequence; each "
                        "result lands as it completes")
    p.add_argument("--manifest", metavar="FILE",
                   help="file of `script.py [args...]` lines, one family per "
                        "line, for per-family arguments")
    p.add_argument("--out", required=True, metavar="DIR",
                   help="output directory. REQUIRED and never inferred: two "
                        "files in this tree inferred their paths by counting "
                        "parent directories and a move pointed them at "
                        "directories that never existed")
    p.add_argument("--python", default=os.environ.get("DESCENT_PY",
                                                      "/usr/bin/python3.12"),
                   help="interpreter for the FAMILY scripts; verified before "
                        "use and never fallen back from (default %(default)s, "
                        "or $DESCENT_PY)")
    p.add_argument("--min-python", default="3.6",
                   help="minimum acceptable family interpreter (default "
                        "%(default)s)")
    p.add_argument("--require-import", action="append", default=[],
                   metavar="MODULE",
                   help="module the family interpreter must be able to import; "
                        "repeatable")
    p.add_argument("--family-arg", action="append", default=[], metavar="ARG",
                   help="argument passed to EVERY family; repeatable. Use "
                        "--manifest for per-family arguments")
    p.add_argument("--baseline", metavar="FILE",
                   help="stored result to compare against. Only meaningful for "
                        "a single family; otherwise each family's "
                        "<stem>_results.json beside its script is used")
    p.add_argument("--no-baseline", action="store_true",
                   help="record the fresh run without comparing")
    p.add_argument("--rtol", type=float, default=DEFAULT_RTOL,
                   help="relative tolerance below which a numeric difference "
                        "is reduction order rather than disagreement "
                        "(default %(default)g)")
    p.add_argument("--atol", type=float, default=DEFAULT_ATOL,
                   help="absolute tolerance (default %(default)g)")
    p.add_argument("--ignore", action="append", default=[], metavar="JSONPATH",
                   help="path to exclude from the comparison, e.g. "
                        "'$.config.jobs'; repeatable. Added to the defaults: "
                        + ", ".join(DEFAULT_IGNORE))
    p.add_argument("--max-examples", type=int, default=50,
                   help="differing leaves listed per category; the true count "
                        "is always reported (default %(default)s)")
    p.add_argument("--timeout", type=float, default=None,
                   help="seconds before a family is killed; a timeout is "
                        "recorded as an outcome, not hidden")
    p.add_argument("--tail", type=int, default=40,
                   help="lines of each stream kept in the summary object "
                        "(the full streams are always on disk)")
    p.add_argument("--allow-unknown-revision", action="store_true",
                   help="record results even when git cannot name the "
                        "revision. Off by default: a result that cannot name "
                        "its revision is a number, not a measurement")
    p.add_argument("--fail-on-diff", action="store_true",
                   help="exit %d if any family differs. OFF by default, "
                        "because a nonzero exit that means 'a difference was "
                        "measured' is exactly the ambiguity this harness "
                        "exists to remove" % EXIT_DIFFERENCES)
    p.add_argument("--simprov", metavar="FILE",
                   help="explicit path to simprov.py, if it has moved")
    return p


def main(argv=None):
    args, unknown = build_parser().parse_known_args(argv)

    jobs = []
    if args.manifest:
        jobs.extend(read_manifest(args.manifest))
    for fam in args.families:
        jobs.append((fam, []))
    if not jobs:
        sys.stderr.write("harness: name at least one family, or --manifest\n")
        return EXIT_HARNESS_ERROR
    shared = list(args.family_arg) + list(unknown)
    jobs = [(script, list(a) + shared) for script, a in jobs]

    if args.baseline and len(jobs) > 1:
        sys.stderr.write("harness: --baseline names one stored result but %d "
                         "families were given; drop it and let each family use "
                         "its own\n" % len(jobs))
        return EXIT_HARNESS_ERROR

    out_root = os.path.abspath(args.out)
    makedirs(out_root)

    repo_root = find_repo_root(__file__)
    simprov, simprov_path = import_simprov(repo_root, args.simprov)

    min_version = tuple(int(x) for x in str(args.min_python).split("."))
    info = verify_interpreter(args.python, min_version, args.require_import)
    if not info["usable"]:
        # Rule 6. Loud, specific, and no fallback: falling back is how the
        # wrong interpreter gets used, and a SyntaxError's nonzero exit is
        # indistinguishable from a finding.
        sys.stderr.write(
            "=" * 78 + "\nVERDICT: NO USABLE INTERPRETER -- NOTHING WAS RUN\n"
            + "=" * 78 + "\n"
            "  requested : %s\n  resolved  : %s\n  problem   : %s\n"
            "  No family was launched and no result was recorded. This is a "
            "refusal,\n  not a finding. Pass --python PATH or set $DESCENT_PY.\n"
            % (info["requested"], info["resolved"], info.get("problem")))
        return EXIT_NO_INTERPRETER

    config = {
        "families": [{"script": s, "args": a} for s, a in jobs],
        "out": out_root, "python": info["resolved"],
        "python_version": info.get("version"),
        "min_python": args.min_python,
        "rtol": args.rtol, "atol": args.atol,
        "ignore": DEFAULT_IGNORE + list(args.ignore),
        "timeout_sec": args.timeout, "no_baseline": args.no_baseline,
        "baseline": args.baseline, "simprov": simprov_path,
        "repo_root": repo_root, "harness_version": HARNESS_VERSION,
    }
    stamp = simprov.stamp("differential/cluster/harness.py", config, None, None)
    if stamp.get("revision") in (None, "", "unknown") and \
            not args.allow_unknown_revision:
        sys.stderr.write(
            "=" * 78 + "\nVERDICT: NO REVISION -- NOTHING WAS RUN\n"
            + "=" * 78 + "\n"
            "  git could not name HEAD for %s, so any result written here "
            "could not\n  say which tree it describes. Refusing rather than "
            "recording an\n  unattributable measurement. Override with "
            "--allow-unknown-revision.\n" % repo_root)
        return EXIT_HARNESS_ERROR

    opts = {
        "python": info["resolved"], "interpreter_info": info,
        "baseline": None if args.no_baseline else args.baseline,
        "rtol": args.rtol, "atol": args.atol,
        "ignore": DEFAULT_IGNORE + list(args.ignore),
        "max_examples": args.max_examples, "timeout": args.timeout,
        "tail": args.tail,
    }

    vault = Vault(os.path.join(out_root, "_vault"))
    summary_txt = os.path.join(out_root, "SUMMARY.txt")
    index_path = os.path.join(out_root, "index.jsonl")

    print("harness: %d families, interpreter %s (%s), revision %s%s"
          % (len(jobs), info["resolved"], info.get("version"),
             str(stamp.get("revision"))[:12],
             "" if stamp.get("workingTreeClean") else " [TREE DIRTY]"))
    print("harness: output %s" % out_root)
    print("harness: a family's nonzero exit is DATA, not a failure")
    print("")

    summaries = []
    write_summary_text(summary_txt, stamp, summaries, opts)

    for script, extra in jobs:
        stem = family_stem(script)
        print("-- running %s %s" % (stem, " ".join(extra)))
        sys.stdout.flush()
        try:
            s = run_family(script, extra, opts, vault, out_root)
        except HarnessError as exc:
            s = {"harness_version": HARNESS_VERSION,
                 "verdict": "HARNESS_ERROR", "verdict_detail": str(exc),
                 "family": {"script": os.path.abspath(script), "stem": stem},
                 "notes": []}
        except Exception as exc:  # a bug here must not cost the other families
            s = {"harness_version": HARNESS_VERSION,
                 "verdict": "HARNESS_ERROR",
                 "verdict_detail": "%s: %s" % (type(exc).__name__, exc),
                 "family": {"script": os.path.abspath(script), "stem": stem},
                 "notes": []}
        s["_provenance"] = stamp

        # Land it NOW. A crash on family seven must not cost families one to
        # six, so nothing is batched to the end.
        run_dir = s.get("run_dir") or os.path.join(out_root, stem)
        makedirs(run_dir)
        fh = open(os.path.join(run_dir, "summary.json"), "w")
        try:
            fh.write(json.dumps(s, indent=1, default=repr) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
        finally:
            fh.close()
        fh = open(index_path, "a")
        try:
            fh.write(json.dumps(s, default=repr) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
        finally:
            fh.close()

        summaries.append(s)
        write_summary_text(summary_txt, stamp, summaries, opts)
        print("   VERDICT %s -- %s" % (s["verdict"], s.get("verdict_detail")))
        sys.stdout.flush()

    text = write_summary_text(summary_txt, stamp, summaries, opts)
    print("")
    print(text)
    print("-> %s" % summary_txt)
    print("-> %s" % index_path)

    differed = [s for s in summaries if s["verdict"] in ALARMING]
    if args.fail_on_diff and differed:
        return EXIT_DIFFERENCES
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
