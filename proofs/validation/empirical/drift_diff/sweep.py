#!/usr/bin/env /usr/bin/python3.12
"""Exact closed-form sweep of taggedDriftR2Ratio vs the simulation-validated form.

The simulation (tag_sym.json) reproduced `correct` to 0 error in exact rational
arithmetic over all replicates, so the closed form may be swept directly:

  Lean:    R2T/R2S = [k VA/(k VA + VE)] / [VA/(VA+VE)]      k = (1-fst)*shared_ld
  Correct: R2T/R2S = k (VA+VE) / ((1-fst) VA + VE)

They agree iff shared_ld = 1.
"""
import json
from fractions import Fraction as F
rows = []
for h2n, h2d in [(2, 10), (5, 10), (8, 10)]:
    VA = F(h2n, h2d); VE = 1 - VA
    for fstn in [0, 6, 12, 24]:
        fst = F(fstn, 100)
        for sln in [100, 70, 50, 34, 20]:
            sl = F(sln, 100)
            k = (1 - fst) * sl
            lean = (k * VA / (k * VA + VE)) / (VA / (VA + VE))
            corr = k * (VA + VE) / ((1 - fst) * VA + VE)
            rows.append(dict(h2=float(VA), fst=float(fst), shared_ld=float(sl),
                             lean=float(lean), correct=float(corr),
                             rel_err_pct=float((lean - corr) / corr * 100),
                             exact_equal=(lean == corr)))
print(json.dumps(rows))
