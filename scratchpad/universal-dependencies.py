from pathlib import Path
import re

root = Path('/projects/standard/hsiehph/sauer354/descent-universal-20260907')
seen = set()
ordered = []

def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = root / (module.replace('.', '/') + '.lean')
    text = source.read_text()
    for dependency in re.findall(r'^import (Descent\.[\w.]+)', text, re.M):
        visit(dependency)
    ordered.append((module, len(text.splitlines())))

visit('Descent.Portability.DiscriminationLaw')
uncached = [(module, lines) for module, lines in ordered
            if not (root / (module.replace('.', '/') + '.olean')).exists()]
print('CLOSURE_MODULES', len(ordered), 'SOURCE_LINES', sum(n for _, n in ordered))
print('UNCACHED_MODULES', len(uncached), 'SOURCE_LINES', sum(n for _, n in uncached))
for module, lines in uncached:
    print(lines, module)
