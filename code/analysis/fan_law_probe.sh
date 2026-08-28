#!/bin/bash
# Regenerates the fan-law table of the companion's sub:fanlaw (Rule 9).
# For f in 4..10, generates the (4,2)-seeded instance at (1,f) and runs the engine with a hard
# node cap; prints RESULT lines whose nodes/depth/prune counts are the table's data.
# The engine binary is built from code/engine/cengine_iso.cpp (see STATUS_TABLE for the command).
# Runtime: f<=7 seconds; f=8,9 minutes; f=10 under an hour on one core (measured 46 min).
set -e
cd "$(dirname "$0")/../.."
ENGINE="${ENGINE:-private/bin/cengine_p7}"
mkdir -p private/inst
for f in 4 5 6 7 8 9 10; do
  inst=private/inst/uni_f${f}_b4c2.txt
  [ -f "$inst" ] || python3 code/engine/gen_basebeta.py 1 $f 4 2 > "$inst"
  echo "=== f=$f ==="
  $ENGINE FILE:$inst 1000000 2>&1 | grep -E "^RESULT"
done
