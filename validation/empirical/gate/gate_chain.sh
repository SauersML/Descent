#!/bin/bash
# BLIND GATE, stage 4: node-side chain.  Detached; independent of any laptop or agent.
#   1. build the analytic tables (pure, pre-seed)
#   2. launch 8 FRESH grid2d seeds (101..108, never used anywhere) through the real
#      P+T pipeline variant
#   3. wait for all sidecars, then run the pinned grader exactly once
# All outputs under theory-out/gate_l3/ and theory-out/gate_{tables,verdict}.json.
set -u
TO=/projects/standard/hsiehph/sauer354/theory-out
GATE=/projects/standard/hsiehph/sauer354/descent/validation/empirical/gate
PY=/projects/standard/hsiehph/sauer354/simcov-venv/bin/python
SIMS=/projects/standard/hsiehph/sauer354/gnomon/sims/ancestry_calibration

$PY "$GATE/gate_tables.py" > "$TO/gate_tables.log" 2>&1 || exit 1
mkdir -p "$TO/gate_l3"
cd "$SIMS" || exit 1
for seed in 101 102 103 104 105 106 107 108; do
  setsid nohup $PY gen_stress_pt.py grid2d "$TO/gate_l3" $seed --tag _gate$seed \
    --threads 3 > "$TO/gate_l3/run_s$seed.log" 2>&1 < /dev/null &
done
# wait for all 8 sidecars (grid2d_realpt_gate<seed>.json), up to 24h
for i in $(seq 1 1440); do
  n=$(ls "$TO"/gate_l3/grid2d_realpt_gate*.json 2>/dev/null | wc -l)
  [ "$n" -ge 8 ] && break
  sleep 60
done
$PY "$GATE/gate_grade.py" > "$TO/gate_verdict.log" 2>&1
