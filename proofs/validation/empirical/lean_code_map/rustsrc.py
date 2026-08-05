"""Name-anchored extraction of Rust function bodies and their numerical-guard surface.

Anchoring is by DECLARATION NAME, never by line number.  `extract/test_parser.py`
is currently failing because it pins absolute line numbers, and a correspondence
table between a Lean corpus and a Rust implementation is the most tempting place
in the repository to make that mistake: locations are the obvious way to write
the mapping down, and they are wrong the moment anybody adds an import.

The content hash is what makes staleness detectable.  A mapped function whose
body changed has an unverified correspondence, which is not the same thing as a
broken one -- so the finding says STALE and names the function, rather than
claiming the mathematics disagrees.

Stdlib only, by CI policy.
"""

import hashlib
import re

_FN = re.compile(r"(?m)^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?(?:const[ \t]+)?fn[ \t]+([A-Za-z_][A-Za-z0-9_]*)")

# Every one of these is a place the mathematics has to say something the clean
# formalization usually assumes away: a clamp, an epsilon, a fallback branch, a
# division, a square root, a NaN test.
GUARD_PATTERNS = (
    ("clamp", re.compile(r"\.clamp\(")),
    ("max", re.compile(r"\.max\(")),
    ("min", re.compile(r"\.min\(")),
    ("epsilon", re.compile(r"EPSILON|f64::MIN_POSITIVE|f32::MIN_POSITIVE")),
    ("small-literal", re.compile(r"\b\d*\.?\d+e-\d+\b")),
    ("is_nan", re.compile(r"\.is_nan\(\)")),
    ("is_finite", re.compile(r"\.is_finite\(\)")),
    ("unwrap_or", re.compile(r"\.unwrap_or(?:_else|_default)?\(")),
    ("sqrt", re.compile(r"\.sqrt\(\)")),
    ("powi", re.compile(r"\.powi\(")),
    ("division", re.compile(r"[A-Za-z0-9_\)\]]\s*/\s*[A-Za-z0-9_\(]")),
    ("recip", re.compile(r"\.recip\(\)")),
)


def _blank_noncode(text):
    """Replace string literals and line comments with spaces of equal length.

    Only used to make brace matching safe; the hash is always taken over the RAW
    text, so this normalisation can never hide a change to the real body.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    break
                j += 1
            for k in range(i, min(j + 1, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def function_bodies(source):
    """{name: raw body text including the outer braces} for every `fn` in `source`.

    A name declared more than once (a trait impl, a test helper) maps to the
    concatenation of all its bodies, so a change to any of them is detected.
    """
    scan = _blank_noncode(source)
    bodies = {}
    for match in _FN.finditer(scan):
        name = match.group(1)
        start = scan.find("{", match.end())
        if start < 0:
            continue
        depth, i, n = 0, start, len(scan)
        while i < n:
            if scan[i] == "{":
                depth += 1
            elif scan[i] == "}":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        if depth != 0:
            continue
        body = source[start:i + 1]
        bodies[name] = bodies.get(name, "") + body
    return bodies


def body_sha256(body):
    """Hash of the body with insignificant whitespace collapsed.

    Reindenting a function is not a change to its mathematics, and a hash that
    fires on reformatting trains people to re-bless the table without reading
    it, which is worse than no hash.
    """
    normalized = re.sub(r"\s+", " ", body).strip()
    return "sha256:" + hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def guard_surface(body):
    """Sorted (kind, count) inventory of the numerical guards inside one body."""
    found = []
    for kind, pattern in GUARD_PATTERNS:
        count = len(pattern.findall(body))
        if count:
            found.append([kind, count])
    return sorted(found)
