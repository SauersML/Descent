"""Independently verify archived branch geometry with exact rational arithmetic."""

from fractions import Fraction as F
import hashlib
import io
import json
from pathlib import Path
import tarfile

import numpy as np


ROOT = Path(__file__).resolve().parent


def centered_rationals(values):
    values = [F(float(x)) for x in values]
    average = sum(values, F(0)) / len(values)
    return [x - average for x in values]


def covariance_coordinates(design, score):
    centered_score = centered_rationals(score)
    return [sum((x * s for x, s in zip(centered_rationals(design[:, j]), centered_score, strict=True)), F(0))
            for j in (0, 1)]


def verify(archive, demography):
    cert = json.load(archive.extractfile(f"{demography}/certificate.json"))
    panel_bytes = archive.extractfile(f"{demography}/panel.npz").read()
    assert hashlib.sha256(panel_bytes).hexdigest() == cert["panel_sha256"]
    with np.load(io.BytesIO(panel_bytes), allow_pickle=False) as panel:
        dosage = panel["dosage"]
        causal = panel["causal_design"]
        score = panel["score"]
        coord, split, distance = panel["coord"], panel["split"], panel["distance"]
        assert np.array_equal(panel["causal_indices"], np.arange(150))
        assert np.all(np.isin(dosage, [0, 1, 2]))
        assert dosage.shape == (cert["n_individuals"], 600)
        assert np.array_equal(causal, (dosage[:, :150].astype(np.float64)
                                      - dosage[:, :150].mean(axis=0, dtype=np.float64)).astype(np.float32))
        frequency = dosage.mean(axis=0, dtype=np.float64) / 2
        assert np.all((frequency >= 0.05) & (frequency <= 0.95))
        assert np.all(np.isfinite(score)) and np.all(np.isin(panel["labels"], [0, 1]))
        assert np.array_equal(panel["labels"], ((np.arange(len(score)) % 7)
                                              < (1 + 2 * dosage[:, 0])).astype(int))

        source_rows = split == "train-deme-test"
        assert source_rows.sum() == 2500
        assert np.all(coord[source_rows] == 0)
        source = causal[source_rows]
        a_s = covariance_coordinates(source, score[source_rows])
        assert [a * 2500 for a in a_s] == list(map(F, cert["source_covariance_numerators"]))

        minor = cert["source_rank_witness"]
        assert minor["columns"] == [0, 1]
        i, j, k = minor["rows"]
        contrast = lambda r, c: F(float(source[r, c])) - F(float(source[i, c]))
        determinant = contrast(j, 0) * contrast(k, 1) - contrast(j, 1) * contrast(k, 0)
        assert determinant == F(minor["determinant"]) and determinant != 0
        pole = [-a_s[1] / a_s[0], F(1)]
        assert a_s[0] * pole[0] + a_s[1] * pole[1] == 0
        source_liability_at_pole = [F(float(x)) * pole[0] + F(float(y))
                                    for x, y in source[:, :2]]
        assert len(set(source_liability_at_pole)) > 1

        target_rows_seen = set()
        for target in cert["targets"]:
            deme = target["deme"]
            rows = (coord == deme) & (split == "other-deme-test")
            assert rows.sum() == 125
            assert np.all(distance[rows] == target["distance"])
            expected_distance = deme if demography == "serial1d" else deme // 6 + deme % 6
            assert target["distance"] == expected_distance
            assert np.ptp(score[rows]) > 0
            a_t = covariance_coordinates(causal[rows], score[rows])
            assert [a * 125 for a in a_t] == list(map(F, target["covariance_numerators"]))
            determinant = (a_s[0] * a_t[1] - a_s[1] * a_t[0]) * 2500 * 125
            assert determinant == F(target["nonparallel_minor"]) and determinant != 0
            assert a_t[0] * pole[0] + a_t[1] * pole[1] != 0
            target_rows_seen.add(deme)
        expected_targets = 9 if demography == "serial1d" else 35
        assert target_rows_seen == set(range(1, expected_targets + 1))

    return {
        "demography": demography, "targets_verified": expected_targets,
        "source_rank_at_least": 2,
        "common_source_zero_direction_first_two_coordinates": list(map(str, pole)),
        "all_target_covariances_nonzero_at_source_zero_direction": True,
        "distance_zero_ratio": 1,
        "positive_distances_with_divergent_ideal_expectation": sorted({t["distance"] for t in cert["targets"]}),
        "panel_sha256": cert["panel_sha256"],
    }


def main():
    path = ROOT / "branch_witnesses.tar.gz"
    with tarfile.open(path) as archive:
        source_contract = json.loads((ROOT / "source_contract.json").read_text())
        for source in source_contract["sources"]:
            content = archive.extractfile("source/" + Path(source["path"]).name).read()
            assert hashlib.sha256(content).hexdigest() == source["sha256"]
        result = {
            "status": "passed",
            "archive_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "certificates": [verify(archive, dem) for dem in ("serial1d", "grid2d")],
            "scope": "exact geometry of checked learner outputs; positive demographic support and divergence are proved analytically in SUPPORT.md and DERIVATION.md",
        }
    (ROOT / "branch_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
