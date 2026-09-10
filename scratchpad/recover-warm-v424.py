"""Read the shared archive cache and recover only the exact pinned revision privately."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import subprocess
import sys

cache = Path('/projects/standard/hsiehph/sauer354/.cache/mathlib')
project = Path('/projects/standard/hsiehph/sauer354/descent-universal-v424-20260907')
needle = b'git=mathlib4@f897ebcf72cd16f89ab4577d0c826cd14afaafc7'
project.mkdir(exist_ok=True)


def matches(path):
    suffix = b''
    with path.open('rb') as archive:
        while chunk := archive.read(1024 * 1024):
            data = suffix + chunk
            if needle in data:
                return path
            suffix = data[-len(needle):]
    return None


if sys.argv[1:] == ['scan']:
    archives = sorted(cache.glob('*.ltar'))
    with ThreadPoolExecutor(max_workers=2) as workers:
        selected = [path for path in workers.map(matches, archives) if path is not None]
    if not selected:
        raise SystemExit('No exact-revision archives found')
    manifest = project / 'matching-archives.json'
    manifest.write_text(json.dumps([str(path) for path in selected]))
    print('SCANNED', len(archives), 'MATCHED', len(selected),
          'COMPRESSED_BYTES', sum(path.stat().st_size for path in selected), flush=True)
    print('MANIFEST', manifest, flush=True)
elif sys.argv[1:] == ['extract']:
    destination = project / 'cache_root'
    destination.mkdir(exist_ok=True)
    with (project / 'matching-archives.json').open('rb') as manifest:
        result = subprocess.run(
            [str(cache / 'leantar-0.1.15'), '-x', '--jobs', '2', '-C', str(destination),
             '-j', '-'], stdin=manifest, timeout=120, check=False)
    if result.returncode:
        raise SystemExit(result.returncode)
    for module in ('Tactic', 'MeasureTheory/Integral/SetIntegral'):
        artifact = destination / '.lake/build/lib/lean/Mathlib' / (module + '.olean')
        print('ARTIFACT', artifact, 'PRESENT', artifact.is_file(), flush=True)
else:
    raise SystemExit('Usage: recover-warm-v424.py scan|extract')
