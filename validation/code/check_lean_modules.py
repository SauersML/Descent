#!/usr/bin/env python3
"""Check selected local Lean sources against the pinned MSI proof cache.

Sources are edited in the repository. Temporary upload bundles and transcripts
live in .git/proof-checks. This checks the named modules, not the entire corpus.
Pass their Check*.lean modules as well to print the transitive theorem axioms.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tarfile
import uuid


def compile_remote(args):
    project = Path(args.cache) / "project"
    mathlib = Path(args.cache) / "mathlib4-f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
    with tarfile.open(args.bundle) as archive:
        for member in archive.getmembers():
            path = Path(member.name)
            if path.is_absolute() or ".." in path.parts or not member.isfile():
                raise ValueError("Invalid source bundle entry: " + member.name)
            if path.suffix != ".lean":
                raise ValueError("Only Lean source files belong in the bundle")
            target = project / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.extractfile(member).read())
    environment = dict(os.environ)
    environment["LEAN_PATH"] = ":".join(
        [str(project), str(mathlib / ".lake/build/lib/lean")]
        + [str(p / ".lake/build/lib/lean") for p in (mathlib / ".lake/packages").iterdir()]
    )
    lean = str(Path(args.cache) / "lean424/bin/lean")

    def ensure_dependency(module):
        if module.startswith("Descent."):
            directory = project
            source = project / (module.replace(".", "/") + ".lean")
            output = source.with_suffix(".olean")
        elif module == "Mathlib" or module.startswith("Mathlib."):
            directory = mathlib
            source = mathlib / (module.replace(".", "/") + ".lean")
            output = mathlib / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        else:
            return
        if output.exists():
            return
        for dependency in re.findall(r"^import\s+(\S+)", source.read_text(), re.M):
            ensure_dependency(dependency)
        output.parent.mkdir(parents=True, exist_ok=True)
        print("Building missing dependency " + module, flush=True)
        subprocess.run([lean, "-j", "2", "-M", "4096", "-o", str(output), str(source)],
                       cwd=str(directory), env=environment, check=True)

    for source in args.sources:
        for dependency in re.findall(r"^import\s+(\S+)", (project / source).read_text(), re.M):
            ensure_dependency(dependency)
        print("Checking " + source, flush=True)
        command = [lean, "-j", "2", "-M", "4096",
                   "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                   "-o", source[:-5] + ".olean", source]
        subprocess.run(command, cwd=str(project), env=environment, check=True)
    print("ALL NAMED MODULES CHECKED", flush=True)


def check_local(args):
    root = Path(__file__).resolve().parents[2]
    import check
    sources = []
    for source in args.sources:
        path = Path(source)
        if path.is_absolute() or ".." in path.parts or path.suffix != ".lean":
            raise ValueError("Expected a repository-relative Lean source: " + source)
        failures = check.style_check_file(root / path)
        if failures:
            raise ValueError("\n".join(failures))
        sources.append(path)
    artifact = root / ".git/proof-checks" / uuid.uuid4().hex
    artifact.mkdir(parents=True)
    bundle = artifact / "sources.tar.gz"
    with tarfile.open(bundle, "w:gz") as archive:
        for source in sources:
            archive.add(root / source, arcname=str(source), recursive=False)
    manifest = {str(p): hashlib.sha256((root / p).read_bytes()).hexdigest() for p in sources}
    (artifact / "hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
    remote_stem = args.shared.rstrip("/") + "/check-" + artifact.name
    subprocess.run([args.msi, "put", str(bundle), remote_stem + ".tar.gz"], check=True)
    subprocess.run([args.msi, "put", str(Path(__file__).resolve()), remote_stem + ".py"], check=True)
    command = ["python3", remote_stem + ".py", "--remote", "--cache", args.cache,
               "--bundle", remote_stem + ".tar.gz", *args.sources]
    result = subprocess.run([args.msi, "-n", args.node, " ".join(map(shlex.quote, command))],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (artifact / "check.log").write_bytes(result.stdout)
    print(result.stdout.decode(), end="")
    print("Check artifacts: " + str(artifact))
    for source, digest in manifest.items():
        if hashlib.sha256((root / source).read_bytes()).hexdigest() != digest:
            raise RuntimeError("Source changed during checking: " + source)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", nargs="+")
    parser.add_argument("--remote", action="store_true")
    parser.add_argument("--bundle")
    parser.add_argument("--msi")
    parser.add_argument("--node", default="acn112")
    parser.add_argument("--cache", default="/tmp/descent-proof-20260910")
    parser.add_argument("--shared", default="/projects/standard/hsiehph/sauer354/portability-lean-20260910")
    parsed = parser.parse_args()
    if parsed.remote:
        compile_remote(parsed)
    elif parsed.msi:
        check_local(parsed)
    else:
        parser.error("Local checking requires --msi with the MSI client path")
