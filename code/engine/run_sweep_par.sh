#!/bin/bash
# Parallel e=1 sweep: like run_sweep.sh (race both mirror representatives per orbit) but running
# SLOTS orbits concurrently.  The sequential runner uses 2 of the machine's cores; this one uses
# 2*SLOTS.  Each orbit writes its verdict to its own log file, so no lock is needed and a label
# can never detach from its verdict; verify_sweep certifies against the directory's *.log glob.
#
#   run_sweep_par.sh <f> <engine-binary> [node-cap] [slots]
set -u
f=${1:?usage: run_sweep_par.sh <f> <engine> [cap] [slots]}
engine=${2:?}
cap=${3:-50000000}
slots=${4:-5}
root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(cd "${SWEEP_DIR:-$PWD}" && pwd)"

prior="$work/.prior_f$f"
grep -ho "f=$f ([0-9]*,[0-9]*): RESULT EXHAUSTED" "$work"/*.log 2>/dev/null \
  | sed -E "s/f=$f \(([0-9]*),([0-9]*)\).*/\1 \2/" | sort -u > "$prior" || true
echo "already exhausted here: $(wc -l < "$prior" | tr -d ' ') instance(s)"

python3 "$root/code/analysis/sweep_configs.py" "$f" > "$work/configs_f$f.txt"

run_word() {  # f bp cp outfile
  local wf=$1 wbp=$2 wcp=$3 wout=$4
  local winst="$work/uni_f${wf}_b${wbp}c${wcp}.txt"
  [ -f "$winst" ] || python3 "$root/code/engine/gen_basebeta.py" 1 "$wf" "$wbp" "$wcp" > "$winst"
  local r
  r=$(CENGINE_GEN=1 CENGINE_THREADS=1 "$engine" "FILE:$winst" "$cap" 2>&1 \
        | grep -oE "RESULT [A-Z_]+ nodes=[0-9]+")
  [ -n "$r" ] && printf "f=%s (%s,%s): %s\n" "$wf" "$wbp" "$wcp" "$r" > "$wout"
}

run_orbit() {  # bp cp
  local bp=$1 cp=$2
  trap 'rm -f "$work/.slot_f${f}_${bp}_${cp}"' EXIT
  local mbp=$((f + 3 - bp)) mcp=$((f + 3 - cp))
  local olog="$work/f${f}_o${bp}_${cp}.log"
  local oA="$work/.rA_${bp}_${cp}" oB="$work/.rB_${bp}_${cp}"
  rm -f "$oA" "$oB"
  run_word "$f" "$bp" "$cp" "$oA" & local pA=$!
  local pB=""
  if [ "$mbp" != "$bp" ] || [ "$mcp" != "$cp" ]; then
    run_word "$f" "$mbp" "$mcp" "$oB" & pB=$!
  fi
  while :; do
    [ -s "$oA" ] && break; [ -s "$oB" ] && break
    kill -0 "$pA" 2>/dev/null || { [ -z "$pB" ] && break; kill -0 "$pB" 2>/dev/null || break; }
    sleep 3
  done
  pkill -f "FILE:$work/uni_f${f}_b${bp}c${cp}.txt" 2>/dev/null
  pkill -f "FILE:$work/uni_f${f}_b${mbp}c${mcp}.txt" 2>/dev/null
  wait "$pA" 2>/dev/null; [ -n "$pB" ] && wait "$pB" 2>/dev/null
  if   [ -s "$oA" ]; then cat "$oA" > "$olog"
  elif [ -s "$oB" ]; then cat "$oB" > "$olog"
  else printf "f=%s (%s,%s): NO RESULT\n" "$f" "$bp" "$cp" > "$olog"
  fi
  rm -f "$oA" "$oB"
  cat "$olog"
}

while read -r line || [ -n "$line" ]; do
  [ -n "$line" ] || continue
  set -- $line
  bp=$2; cp=$3
  mbp=$((f + 3 - bp)); mcp=$((f + 3 - cp))
  if grep -qx "$bp $cp" "$prior" 2>/dev/null || grep -qx "$mbp $mcp" "$prior" 2>/dev/null; then
    continue
  fi
  # Throttle on token files the PARENT creates synchronously before spawning; the orbit removes
  # its token on exit (trap EXIT).  Three live failures behind this design: `jobs` in a subshell
  # missed the job table (39 engines); `pgrep -c || echo 0` printed two zeros on no-match so the
  # test errored and nothing throttled (1252 engines, load 279); counting engine processes raced
  # against their startup latency (40 engines).  Tokens have no startup latency.
  while [ "$(ls "$work"/.slot_f${f}_* 2>/dev/null | wc -l | tr -d ' ')" -ge "$slots" ]; do
    sleep 3
  done
  : > "$work/.slot_f${f}_${bp}_${cp}"
  run_orbit "$bp" "$cp" &
done < "$work/configs_f$f.txt"
wait

echo "--- coverage certificate ---"
python3 "$root/code/analysis/verify_sweep.py" "$f" "$work"/*.log 2>/dev/null | tail -2
