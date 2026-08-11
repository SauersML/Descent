#!/usr/bin/env python3
"""Exact witness for pangenome presentation invariance.

The same three haplotypes are segmented into long, atomic, mixed, and relabelled graph
nodes.  Every presentation retains stable semantic atoms, so this is a controlled test of
lossless node splitting, merging, and relabelling.  No model is fitted and no randomness is
used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


HERE = Path(__file__).resolve().parent

BASES = {
    "p0": "A",
    "p1": "C",
    "p2": "G",
    "a": "T",
    "b": "C",
    "r0": "G",
    "r1": "G",
    "r2": "A",
}

HAPLOTYPES = {
    "h1": ("p0", "p1", "p2", "a", "r0", "r1", "r2"),
    "h2": ("p0", "p1", "p2", "b", "r0", "r1", "r2"),
    "h3": ("p0", "p1", "p2", "b", "r0", "r1", "r2"),
}


@dataclass(frozen=True)
class Presentation:
    """A segmentation of the fixed semantic atom paths into named graph nodes."""

    blocks: dict[str, tuple[str, ...]]
    paths: dict[str, tuple[str, ...]]

    def validate(self) -> None:
        assert set(self.paths) == set(HAPLOTYPES)
        assert all(block for block in self.blocks.values())
        for haplotype, path in self.paths.items():
            assert all(node in self.blocks for node in path)
            expanded = tuple(atom for node in path for atom in self.blocks[node])
            assert expanded == HAPLOTYPES[haplotype]
        assert set().union(*(set(block) for block in self.blocks.values())) == set(BASES)


def presentations() -> dict[str, Presentation]:
    coarse = Presentation(
        blocks={
            "left": ("p0", "p1", "p2"),
            "allele_a": ("a",),
            "allele_b": ("b",),
            "right": ("r0", "r1", "r2"),
        },
        paths={
            "h1": ("left", "allele_a", "right"),
            "h2": ("left", "allele_b", "right"),
            "h3": ("left", "allele_b", "right"),
        },
    )
    atomic = Presentation(
        blocks={atom: (atom,) for atom in BASES},
        paths={haplotype: atoms for haplotype, atoms in HAPLOTYPES.items()},
    )
    mixed = Presentation(
        blocks={
            "left_0": ("p0",),
            "left_12": ("p1", "p2"),
            "allele_a": ("a",),
            "allele_b": ("b",),
            "right_01": ("r0", "r1"),
            "right_2": ("r2",),
        },
        paths={
            "h1": ("left_0", "left_12", "allele_a", "right_01", "right_2"),
            "h2": ("left_0", "left_12", "allele_b", "right_01", "right_2"),
            "h3": ("left_0", "left_12", "allele_b", "right_01", "right_2"),
        },
    )
    relabelled = Presentation(
        blocks={f"node_{index + 17}": block for index, block in enumerate(coarse.blocks.values())},
        paths={
            "h1": ("node_17", "node_18", "node_20"),
            "h2": ("node_17", "node_19", "node_20"),
            "h3": ("node_17", "node_19", "node_20"),
        },
    )
    result = {
        "coarse": coarse,
        "atomic": atomic,
        "mixed": mixed,
        "relabelled": relabelled,
    }
    for presentation in result.values():
        presentation.validate()
    return result


def spelled_haplotypes(presentation: Presentation) -> dict[str, str]:
    return {
        haplotype: "".join(
            BASES[atom] for node in path for atom in presentation.blocks[node]
        )
        for haplotype, path in presentation.paths.items()
    }


def semantic_kernel() -> list[tuple[tuple[str, int], tuple[str, int]]]:
    occurrences = [
        (haplotype, index, atom)
        for haplotype, atoms in HAPLOTYPES.items()
        for index, atom in enumerate(atoms)
    ]
    return [
        ((left_haplotype, left_index), (right_haplotype, right_index))
        for left_haplotype, left_index, left_atom in occurrences
        for right_haplotype, right_index, right_atom in occurrences
        if left_atom == right_atom
    ]


def kernel_digest() -> str:
    payload = json.dumps(semantic_kernel(), separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode()).hexdigest()


def atom_support_histogram() -> dict[str, int]:
    support = {
        atom: sum(atom in atoms for atoms in HAPLOTYPES.values())
        for atom in BASES
    }
    return {str(size): count for size, count in sorted(Counter(support.values()).items())}


def node_support_histogram(presentation: Presentation) -> dict[str, int]:
    support = {
        node: sum(node in path for path in presentation.paths.values())
        for node in presentation.blocks
    }
    return {str(size): count for size, count in sorted(Counter(support.values()).items())}


def edge_count(presentation: Presentation) -> int:
    return len(
        {
            edge
            for path in presentation.paths.values()
            for edge in zip(path, path[1:])
        }
    )


def pairwise_hamming_sum(sequences: dict[str, str]) -> int:
    names = sorted(sequences)
    return sum(
        sum(left != right for left, right in zip(sequences[a], sequences[b]))
        for i, a in enumerate(names)
        for b in names[i + 1 :]
    )


def measure(presentation: Presentation) -> dict[str, object]:
    sequences = spelled_haplotypes(presentation)
    invariant = {
        "spelled_haplotypes": sequences,
        "semantic_kernel_sha256": kernel_digest(),
        "semantic_coordinate_count": len(BASES),
        "atom_support_histogram": atom_support_histogram(),
        "weighted_support_mass": sum(len(atoms) for atoms in HAPLOTYPES.values()),
        "pairwise_hamming_sum": pairwise_hamming_sum(sequences),
    }
    presentation_dependent = {
        "node_count": len(presentation.blocks),
        "edge_count": edge_count(presentation),
        "node_support_histogram": node_support_histogram(presentation),
    }
    return {"invariant": invariant, "presentation_dependent": presentation_dependent}


def run() -> dict[str, object]:
    measurements = {name: measure(value) for name, value in presentations().items()}
    invariants = [entry["invariant"] for entry in measurements.values()]
    dependent = [entry["presentation_dependent"] for entry in measurements.values()]
    assert all(value == invariants[0] for value in invariants[1:])
    assert len({json.dumps(value, sort_keys=True) for value in dependent}) > 1
    return {
        "claim": "kernel statistics survive lossless presentation rewrites; node statistics need not",
        "presentations": measurements,
        "checks": {
            "all_semantic_invariants_equal": True,
            "some_node_statistics_differ": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        (HERE / "results.json").write_text(rendered, encoding="utf-8")
    else:
        committed = json.loads((HERE / "results.json").read_text(encoding="utf-8"))
        assert committed == result
        print(rendered, end="")


if __name__ == "__main__":
    main()
