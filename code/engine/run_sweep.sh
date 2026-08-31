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

# Scope: skip instances already exhausted in any log of this directory.  Two stale drivers were
# found on 2026-08-31 re-deciding f=12 and f=14 words that the current engine settles in under a
# thousand nodes -- one had burned 27 hours of CPU.  A sweep should never repeat settled work.
prior="$work/.prior_f$f"
: > "$prior"
grep -ho "f=$f ([0-9]*,[0-9]*): RESULT EXHAUSTED" "$work"/*.log 2>/dev/null \
  | sed -E "s/f=$f \(([0-9]*),([0-9]*)\).*/\1 \2/" | sort -u > "$prior" || true
nprior=$(wc -l < "$prior" | tr -d " ")
echo "already exhausted in this directory: $nprior instance(s) -- these are skipped"

# the log is appended to, never truncated: it is the evidence the certificate reads, and
# truncating it would make the next run repeat everything.
touch "$log"

python3 "$root/code/analysis/sweep_configs.py" "$f" > "$work/configs_f$f.txt"


# Race both representatives of each mirror orbit.  `sweep_configs.transversal` returns "the member
# with the smaller bp", one fixed representative per orbit -- and search cost turns out to be
# strongly direction-dependent.  On f=22 the two orbits {(12,20),(13,5)} and {(12,23),(13,2)} cost
# 869 and 928 CPU-minutes through their bp=12 representatives without finishing, while their mirrors
# exhausted in about seven minutes each: four orders of magnitude.  verify_sweep has always credited
# an orbit when the word OR its mirror is exhausted, so racing both costs at most 2x the cheaper one
# instead of paying the dearer one in full.
#
# Each word writes to its own file and its label is printed by the same code that reads its result,
# so a label can never detach from its verdict -- the failure that made four f=22 results
# unattributable and forced a re-run.
run_word() {
  local wf=$1 wbp=$2 wcp=$3 wout=$4
  local winst="$work/uni_f${wf}_b${wbp}c${wcp}.txt"
  [ -f "$winst" ] || python3 "$root/code/engine/gen_basebeta.py" 1 "$wf" "$wbp" "$wcp" > "$winst"
  local r
  r=$(CENGINE_GEN=1 CENGINE_THREADS=1 "$engine" "FILE:$winst" "$cap" 2>&1 \
        | grep -oE "RESULT [A-Z_]+ nodes=[0-9]+")
  [ -n "$r" ] && printf "f=%s (%s,%s): %s\n" "$wf" "$wbp" "$wcp" "$r" > "$wout"
}

while read -r line || [ -n "$line" ]; do
  [ -n "$line" ] || continue
  set -- $line
  bp=$2; cp=$3
  mbp=$((f + 3 - bp)); mcp=$((f + 3 - cp))
  if grep -qx "$bp $cp" "$prior" 2>/dev/null || grep -qx "$mbp $mcp" "$prior" 2>/dev/null; then
    echo "f=$f ($bp,$cp): SKIPPED (orbit already exhausted)"
    continue
  fi
  oA="$work/.race_A.$$"; oB="$work/.race_B.$$"; rm -f "$oA" "$oB"
  run_word "$f" "$bp" "$cp" "$oA" & pA=$!
  pB=""
  if [ "$mbp" != "$bp" ] || [ "$mcp" != "$cp" ]; then
    run_word "$f" "$mbp" "$mcp" "$oB" & pB=$!
  fi
  # wait for the first verdict; stop when neither child is still alive
  while :; do
    [ -s "$oA" ] && break
    [ -s "$oB" ] && break
    kill -0 "$pA" 2>/dev/null || { [ -z "$pB" ] && break; kill -0 "$pB" 2>/dev/null || break; }
    sleep 2
  done
  kill "$pA" 2>/dev/null; [ -n "$pB" ] && kill "$pB" 2>/dev/null
  pkill -P "$pA" 2>/dev/null; [ -n "$pB" ] && pkill -P "$pB" 2>/dev/null
  wait "$pA" 2>/dev/null; [ -n "$pB" ] && wait "$pB" 2>/dev/null
  if [ -s "$oA" ]; then cat "$oA" | tee -a "$log"
  elif [ -s "$oB" ]; then cat "$oB" | tee -a "$log"
  else printf "f=%s (%s,%s): NO RESULT\n" "$f" "$bp" "$cp" | tee -a "$log"
  fi
  rm -f "$oA" "$oB"
done < "$work/configs_f$f.txt"

echo "--- coverage certificate ---"
# certify against every log in the directory, not just this run's: skipped instances were
# exhausted in an earlier run and their evidence lives there.
python3 "$root/code/analysis/verify_sweep.py" "$f" "$work"/*.log 2>/dev/null | tail -2
