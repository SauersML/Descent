"""Rebuild held-out portability curves from archived simulation summaries.

Run: uv run --with-requirements requirements.txt python plot_portability_ci.py
The archive contains the original, unmodified per-deme summaries and run metadata.
No fitted demographic law or digitized values from a figure are used.
"""

from __future__ import annotations

import csv
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "inputs.tar.gz"
SNAPSHOT = (
    "/projects/standard/hsiehph/sauer354/.snapshot/"
    "snapshot_2026-08-16_00_00_00_UTC/gnomon/sims/"
    "results_hpc/ancestry_calibration/data"
)
BOOTSTRAPS = 50_000
RNG_SEED = 20260910


def write_csv(name, rows):
    with (ROOT / name).open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def load_runs():
    records = []
    files = []
    protocols = {}
    with tarfile.open(ARCHIVE) as archive:
        for member in sorted(archive.getmembers(), key=lambda x: x.name):
            match = re.fullmatch(
                r"(grid2d|serial1d)_phenoA_realpt_s(\d+)\.sanity\.tsv", member.name
            )
            if match is None:
                continue
            dem, seed_text = match.groups()
            seed = int(seed_text)
            content = archive.extractfile(member).read()
            rows = list(csv.DictReader(io.StringIO(content.decode()), delimiter="\t"))
            metadata = json.load(archive.extractfile(f"{dem}_realpt_s{seed}.json"))
            assert metadata["dem"] == dem and metadata["seed"] == seed
            assert len(rows) == (36 if dem == "grid2d" else 10)
            assert len({row["deme"] for row in rows}) == len(rows)
            train = [row for row in rows if row["is_training_ancestry"] == "True"]
            assert len(train) == 1
            assert int(train[0]["deme"]) == metadata["train_deme"]
            assert float(train[0]["dist"]) == 0
            source_r2 = float(train[0]["corr_pgs_true_liab_test"]) ** 2
            assert np.isfinite(source_r2) and source_r2 > 0
            parameters = metadata["params"]
            protocol = (
                metadata["n_total"], metadata["sigma_e"], metadata["prev_target"],
                parameters["n_chunks"], parameters["chunk_bp"],
                parameters["mu"], parameters["recomb"], metadata["pgs_method"],
            )
            if dem in protocols:
                assert protocol == protocols[dem], (dem, seed, "protocol changed")
            protocols[dem] = protocol
            for row in rows:
                correlation = float(row["corr_pgs_true_liab_test"])
                distance = float(row["dist"])
                assert np.isfinite(correlation) and -1 <= correlation <= 1
                assert distance.is_integer() and int(row["n_test"]) > 2
                r2 = correlation ** 2
                records.append(dict(
                    demography=dem, seed=seed, deme=int(row["deme"]),
                    distance=int(distance), n_test=int(row["n_test"]),
                    r2=r2, source_r2=source_r2, ratio=r2 / source_r2,
                ))
            files.append(dict(name=member.name, sha256=hashlib.sha256(content).hexdigest()))
    assert len(records) > 0
    return records, files


def summarize(records):
    # Each run first contributes one equal-deme average at each available distance.
    # Then every run receives equal weight. A whole run is the bootstrap unit:
    # all target ratios sharing a trained score and source denominator stay together.
    summaries = []
    per_seed = []
    rng = np.random.default_rng(RNG_SEED)
    for dem in ("grid2d", "serial1d"):
        seeds = sorted({r["seed"] for r in records if r["demography"] == dem})
        distances = sorted({r["distance"] for r in records if r["demography"] == dem})
        values = np.full((len(seeds), len(distances), 2), np.nan)
        for i, seed in enumerate(seeds):
            for j, distance in enumerate(distances):
                subset = [r for r in records if r["demography"] == dem
                          and r["seed"] == seed and r["distance"] == distance]
                if not subset:
                    continue
                values[i, j] = [np.mean([r[k] for r in subset]) for k in ("r2", "ratio")]
                per_seed.append(dict(
                    demography=dem, seed=seed, distance=distance, n_demes=len(subset),
                    r2=values[i, j, 0], ratio=values[i, j, 1],
                ))
        assert np.all(values[:, 0, 1] == 1)
        draws = rng.integers(0, len(seeds), size=(BOOTSTRAPS, len(seeds)))
        for j, distance in enumerate(distances):
            sampled = values[draws, j, :]
            counts = np.isfinite(sampled[:, :, 0]).sum(axis=1)
            valid = counts > 0
            bootstrap_means = np.nansum(sampled[valid], axis=1) / counts[valid, None]
            n_seeds = int(np.isfinite(values[:, j, 0]).sum())
            assert n_seeds >= 2, (dem, distance, "not enough independent runs for a CI")
            for k, metric in enumerate(("r2", "ratio")):
                lo, hi = np.quantile(bootstrap_means[:, k], [0.025, 0.975])
                summaries.append(dict(
                    demography=dem, distance=distance, metric=metric,
                    mean=float(np.nanmean(values[:, j, k])),
                    ci95_low=float(lo), ci95_high=float(hi), n_seeds=n_seeds,
                    bootstrap_replicates_valid=int(valid.sum()),
                    bootstrap_replicates_without_distance=int((~valid).sum()),
                ))
    return per_seed, summaries


def plot(summaries, metric, filename):
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 11,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#b7bbc2", "axes.labelcolor": "#252d39",
        "text.color": "#252d39", "xtick.color": "#555e6a", "ytick.color": "#555e6a",
        "figure.facecolor": "white", "savefig.facecolor": "white",
    })
    fig, axes = plt.subplots(1, 2, figsize=(12.2, 6.5), sharey=True)
    fig.subplots_adjust(left=.085, right=.975, bottom=.25, top=.75, wspace=.13)
    title = "Polygenic score accuracy retained away from training" if metric == "ratio" else "Polygenic score accuracy away from training"
    fig.suptitle(title, x=.085, y=.965, ha="left", fontsize=19, fontweight="bold")
    fig.text(.085, .904, "Held-out squared correlation with true liability · phenoA · real GWAS + clumping + thresholding", fontsize=10.7)
    interval_label = "bootstrap intervals" if metric == "ratio" else "bootstrap CIs"
    fig.text(.085, .858, f"Mean across 11 recovered runs per demography; bars and shading: pointwise 95% {interval_label}", fontsize=10.5, color="#596272")
    all_upper = [r["ci95_high"] for r in summaries if r["metric"] == metric]
    for ax, (dem, label, color, marker) in zip(axes, [
        ("grid2d", "2-D grid", "#c0453b", "o"),
        ("serial1d", "1-D chain", "#3e5c76", "s"),
    ]):
        rows = [r for r in summaries if r["demography"] == dem and r["metric"] == metric]
        x = np.array([r["distance"] for r in rows])
        mean = np.array([r["mean"] for r in rows])
        low = np.array([r["ci95_low"] for r in rows])
        high = np.array([r["ci95_high"] for r in rows])
        ax.set_title(label, loc="left", fontweight="bold", pad=17, color=color)
        ax.grid(axis="y", color="#e9ebee", linewidth=.8)
        ax.set_axisbelow(True)
        ax.fill_between(x, low, high, color=color, alpha=.12, linewidth=0)
        ax.vlines(x, low, high, color=color, linewidth=1.4)
        ax.hlines(low, x-.08, x+.08, color=color, linewidth=1.4)
        ax.hlines(high, x-.08, x+.08, color=color, linewidth=1.4)
        ax.plot(x, mean, color=color, marker=marker, linewidth=2.1,
                markersize=5.5, markeredgecolor="white", markeredgewidth=.8)
        if metric == "ratio":
            ax.axhline(1, color="#858c95", linewidth=1, linestyle=(0, (4, 4)))
        ax.set_xlabel("Distance from training population (deme steps)", labelpad=11)
        ax.set_xticks(np.arange(11))
        ax.set_xlim(-.25, 10.3)
        ax.set_ylim(0, max(all_upper) * 1.12)
        for row in rows:
            ax.text(row["distance"], -.22, str(row["n_seeds"]),
                    transform=ax.get_xaxis_transform(), ha="center", va="top",
                    fontsize=9, color="#6a717b")
    axes[0].set_ylabel("Accuracy ratio: target R² / training-population R²" if metric == "ratio" else "Squared correlation (R²)", labelpad=12)
    fig.text(.018, .13, "Runs:", fontsize=9, color="#6a717b")
    fig.text(.085, .077, "Entire runs are resampled together. Deme ratios are averaged within each run and distance, then across runs.", fontsize=9, color="#596272")
    footer = ("Descriptive bootstrap intervals for the recovered runs. An exact demographic prediction for this curve has not been derived."
              if metric == "ratio" else
              "Far distances occur in fewer runs (counts above); intervals there are less reliable. CIs describe the mean, not the spread of individual runs.")
    fig.text(.085, .040, footer, fontsize=9, color="#596272")
    fig.savefig(ROOT / f"{filename}.png", dpi=220)
    fig.savefig(ROOT / f"{filename}.pdf")
    plt.close(fig)


def main():
    records, files = load_runs()
    per_seed, summaries = summarize(records)
    write_csv("per_deme_accuracy.csv", records)
    write_csv("per_seed_distance.csv", per_seed)
    write_csv("confidence_intervals.csv", summaries)
    manifest = dict(
        snapshot=SNAPSHOT, archive_sha256=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
        source_files=files, bootstrap_replicates=BOOTSTRAPS, bootstrap_seed=RNG_SEED,
        ci_method="pointwise percentile bootstrap, resampling whole simulation seeds within demography",
        metric="within-deme held-out squared Pearson correlation of PGS and true_liab",
        averaging="mean of target/source R2 ratios within seed and distance; equal-weight mean of available seeds",
        distance_conditioning="only runs containing a target at this distance contribute",
        limitation="11 recoverable runs per demography; far distances have fewer contributing runs; not simultaneous confidence bands",
        ratio_expectation="not established; previous completion and applicability claims withdrawn; bootstrap bars describe recovered-run resampling; see ../portability_expectation/AUDIT.md",
        seeds=sorted({r["seed"] for r in records}),
        missing_summaries_for_metadata_seeds=list(range(11, 96)),
        original_image="best4_rawpgs_vs_fst.png was a migration sweep; this artifact is the requested within-history distance curve, not that image with added error bars",
    )
    (ROOT / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    plot(summaries, "r2", "accuracy_by_distance_95ci")
    plot(summaries, "ratio", "accuracy_ratio_by_distance_95ci")
    print(f"Validated {len(files)} run summaries, {len(records)} deme measurements.")
    print(f"Seeds: {manifest['seeds']}")
    for dem in ("grid2d", "serial1d"):
        rows = [r for r in summaries if r["demography"] == dem and r["metric"] == "ratio"]
        print(dem, [(r["distance"], round(r["mean"], 3), r["n_seeds"]) for r in rows])


if __name__ == "__main__":
    main()
