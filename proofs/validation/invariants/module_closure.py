"""Fail when a Calibrator Lean module is outside the root import closure.

`lake build Calibrator` can only validate modules reachable from
`proofs/Calibrator.lean`.  This check compares that transitive closure with the
source tree, so adding an unimported module cannot produce a false-green root
build.
"""

from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[3]
PROOFS = REPO / "proofs"
ROOT = PROOFS / "Calibrator.lean"
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")


def module_path(module):
    return PROOFS / (module.replace(".", "/") + ".lean")


def direct_imports(path):
    imports = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if match is not None:
            imports.add(match.group(1))
    return imports


def calibrator_sources():
    modules = {
        path
        for path in (PROOFS / "Calibrator").rglob("*.lean")
        if not any(part.startswith("._") for part in path.parts)
    }
    return {ROOT, *modules}


def root_closure():
    closure = {ROOT}
    pending = list(direct_imports(ROOT))
    seen_modules = set()
    while pending:
        module = pending.pop()
        if module in seen_modules:
            continue
        seen_modules.add(module)
        path = module_path(module)
        if not path.is_file():
            continue
        closure.add(path)
        pending.extend(direct_imports(path) - seen_modules)
    return closure


def main():
    sources = calibrator_sources()
    closure = root_closure()
    absent = sorted(path.relative_to(REPO) for path in sources - closure)
    print(f"CALIBRATOR_SOURCES\t{len(sources)}")
    print(f"ROOT_CLOSURE\t{len(closure & sources)}")
    for path in absent:
        print(f"MODULE_ABSENT\t{path}")
    if absent:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
