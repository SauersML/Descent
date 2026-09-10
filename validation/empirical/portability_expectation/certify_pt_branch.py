"""Construct a positive-support genotype/label branch and run the recovered P+T.

This is a support witness for DERIVATION.md, not a typical demographic draw or
an estimate of mean accuracy. The learner and BED writer are imported unchanged
from the explicitly supplied, hash-checked archived source directory.
"""

import argparse
from fractions import Fraction
import hashlib
import importlib
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys

import numpy as np
from sklearn.decomposition import PCA
from sklearn.preprocessing import StandardScaler
from threadpoolctl import threadpool_limits


SOURCE_HASHES = {
    "gen_real_pt.py": "53e677c1f756aa15c36506fcea6b7ce14db27fabe6e1a4a1bec659b438e2c9ba",
    "stream_geno.py": "8a87fa798f6c680cd52b86a25251894a1576201ea7114c7e98ceb7726fdf02c4",
}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact_covariance_numerator(genotype, score):
    # n * sum(x*s) - sum(x)*sum(s): proportional to C^T centered_score.
    # float.as_integer_ratio preserves each returned score exactly.
    scores = [Fraction(float(s)) for s in score]
    genotypes = [Fraction(float(x)) for x in genotype]
    return (len(scores) * sum((x * s for x, s in zip(genotypes, scores, strict=True)), Fraction(0))
            - sum(genotypes, Fraction(0)) * sum(scores, Fraction(0)))


def rank_two_minor(genotypes):
    # Two independent differences between observed rows certify centered rank >= 2.
    base = [Fraction(float(x)) for x in genotypes[0, :2]]
    differences = [[Fraction(float(row[j])) - base[j] for j in (0, 1)]
                   for row in genotypes]
    for i in range(1, len(differences)):
        for j in range(i + 1, len(differences)):
            det = (differences[i][0] * differences[j][1]
                   - differences[i][1] * differences[j][0])
            if det:
                return {"rows": [0, i, j], "columns": [0, 1], "determinant": str(det)}
    raise AssertionError("The constructed source panel has no rank-two witness")


def run(args):
    source_dir = Path(args.source).resolve()
    for filename, expected in SOURCE_HASHES.items():
        assert sha256(source_dir / filename) == expected, filename
    sys.path.insert(0, str(source_dir))
    simulator = importlib.import_module("gen_real_pt")
    writer = importlib.import_module("stream_geno")
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=False)

    _, _, coord, distance, training_deme, npc = simulator.DEMS[args.demography](train_deme=0)
    n = len(coord)
    n_variants = 600
    rng = np.random.default_rng(20260910)
    # A compact support witness. Every biallelic haplotype array used here has
    # positive probability under a finite JC69-mutated genealogy; see SUPPORT.md.
    dosage = rng.binomial(2, 0.3, size=(n, n_variants)).astype(np.float32)
    maf = np.minimum(dosage.mean(axis=0) / 2, 1 - dosage.mean(axis=0) / 2)
    assert np.all(maf >= 0.05)
    causal_indices = np.arange(150)
    # Retain the actual float32 preprocessing output as an exact fixed design.
    # Subtraction rounding can prevent raw integer-column contrasts from being
    # identical to this matrix's contrasts, so the certificate uses this matrix.
    causal_design = StandardScaler(with_std=False).fit_transform(dosage[:, causal_indices])
    split = np.empty(n, dtype="U20")
    for deme in np.unique(coord):
        rows = np.flatnonzero(coord == deme)
        half = len(rows) // 2
        prefix = "train" if deme == training_deme else "other"
        split[rows[:half]] = f"{prefix}-deme-fit"
        split[rows[half:]] = f"{prefix}-deme-test"
    labels = ((np.arange(n) % 7) < (1 + 2 * dosage[:, 0])).astype(int)

    with threadpool_limits(limits=2):
        pcs = PCA(6, svd_solver="randomized", random_state=0).fit_transform(
            StandardScaler().fit_transform(dosage))
        pcs = StandardScaler().fit_transform(pcs)[:, :npc]

    prefix = out / "geno"
    with Path(str(prefix) + ".bed").open("wb") as bed:
        bed.write(bytes([0x6c, 0x1b, 0x01]))
        writer._write_bed_block(dosage, bed)
    with Path(str(prefix) + ".bim").open("w") as bim:
        for index in range(n_variants):
            chromosome = index // 30 + 1
            position = (index % 30 + 1) * 100_000
            bim.write(f"{chromosome}\tsnp{chromosome}_{position}_{index}\t0\t{position}\tA\tG\n")
    with Path(str(prefix) + ".fam").open("w") as fam:
        fam.writelines(f"i{i}\ti{i}\t0\t0\t0\t-9\n" for i in range(n))

    score, pt_metadata = simulator.real_pt(
        str(prefix), n, coord, training_deme, labels, pcs, npc, split,
        str(out / "pt"), threads=2, mem_mb=2000)
    assert np.all(np.isfinite(score))
    source_rows = split == "train-deme-test"
    source_causal = causal_design[source_rows]
    source_score = score[source_rows]
    rank_certificate = rank_two_minor(source_causal)
    a_s = [exact_covariance_numerator(source_causal[:, j], source_score) for j in (0, 1)]
    assert any(a_s)
    assert np.ptp(source_score) > 0
    target_certificates = []
    for deme in np.unique(coord):
        if deme == training_deme:
            continue
        rows = (coord == deme) & (split == "other-deme-test")
        target_causal = causal_design[rows]
        target_score = score[rows]
        a_t = [exact_covariance_numerator(target_causal[:, j], target_score) for j in (0, 1)]
        determinant = a_s[0] * a_t[1] - a_s[1] * a_t[0]
        assert determinant != 0, int(deme)
        assert np.ptp(target_score) > 0
        target_certificates.append({
            "deme": int(deme), "distance": int(distance[rows][0]),
            "n_test": int(rows.sum()),
            "covariance_numerators": [str(x) for x in a_t],
            "nonparallel_minor": str(determinant),
        })

    np.savez_compressed(
        out / "panel.npz", dosage=dosage, causal_indices=causal_indices, causal_design=causal_design,
        score=score, labels=labels, pcs=pcs, coord=coord, distance=distance, split=split)
    certificate = {
        "status": "all target branches certified",
        "demography": args.demography, "training_deme": int(training_deme),
        "n_individuals": n, "n_variants": n_variants, "n_causal": 150,
        "n_source_test": int(source_rows.sum()),
        "source_rank_witness": rank_certificate,
        "source_covariance_numerators": [str(x) for x in a_s],
        "targets": target_certificates,
        "pt": pt_metadata,
        "source_sha256": SOURCE_HASHES,
        "plink": {name: {"path": str(path), "sha256": sha256(path),
                          "version": subprocess.check_output([path, "--version"], text=True).strip()}
                  for name, path in (("plink1", simulator.PLINK1), ("plink2", simulator.PLINK2))},
        "packages": {name: importlib.metadata.version(name)
                     for name in ("numpy", "pandas", "scipy", "scikit-learn", "msprime", "tskit", "threadpoolctl")},
        "panel_sha256": sha256(out / "panel.npz"),
        "causal_design_semantics": "fixed float32 StandardScaler output, interpreted exactly in the continuous-effect readout",
        "interpretation": "positive-support witness, not a typical draw or a mean estimate",
    }
    (out / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    print(json.dumps(certificate, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, help="directory with hash-matched recovered Python sources")
    parser.add_argument("--demography", required=True, choices=("serial1d", "grid2d"))
    parser.add_argument("--output", required=True, help="new directory for the complete branch witness")
    run(parser.parse_args())
