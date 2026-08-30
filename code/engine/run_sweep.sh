#!/bin/bash
# Canonical e=1 sweep at a given f: generate the instances, run them, certify the coverage.
#
#   run_sweep.sh <f> <engine-binary> [node-cap]
#
# The instance list comes from code/analysis/sweep_configs.py (one representative per mirror
# orbit at the proved reach), and code/analysis/verify_sweep.py certifies at the end that every
# escaping base word is exhausted or has an exhausted mirror.
#
# The `|| [ -n "$line" ]` is not decoration: the ad hoc drivers that preceded this script fed
# their lists to a bare `while read`, which drops a final line carrying no newline, and that
# silently cost one orbit in each of the f=14 and f=18 sweeps.
set -u
f=${1:?usage: run_sweep.sh <f> <engine-binary> [node-cap]}
engine=${2:?usage: run_sweep.sh <f> <engine-binary> [node-cap]}
cap=${3:-50000000}
root="$(cd "$(dirname "$0")/../.." && pwd)"
work="${SWEEP_DIR:-$PWD}"
log="$work/sweep_f$f.log"
: > "$log"

python3 "$root/code/analysis/sweep_configs.py" "$f" > "$work/configs_f$f.txt"

while read -r line || [ -n "$line" ]; do
  [ -n "$line" ] || continue
  set -- $line
  bp=$2; cp=$3
  inst="$work/uni_f${f}_b${bp}c${cp}.txt"
  [ -f "$inst" ] || python3 "$root/code/engine/gen_basebeta.py" 1 "$f" "$bp" "$cp" > "$inst"
  printf "f=%s (%s,%s): " "$f" "$bp" "$cp" | tee -a "$log"
  CENGINE_GEN=1 CENGINE_THREADS=1 "$engine" "FILE:$inst" "$cap" 2>&1 \
    | grep -oE "RESULT [A-Z_]+ nodes=[0-9]+" | tee -a "$log" || echo "NO RESULT" | tee -a "$log"
done < "$work/configs_f$f.txt"

echo "--- coverage certificate ---"
python3 "$root/code/analysis/verify_sweep.py" "$f" "$log" 2>/dev/null | tail -2
