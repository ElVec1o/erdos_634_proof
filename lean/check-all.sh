#!/bin/bash
# check-all.sh — verify the whole Erdos634 corpus.
#
# Why this exists rather than `lake build`: the modules live at lean/X.lean but are imported as
# Erdos634.X, with oleans hand-placed under build/Erdos634/. Lake, whose srcDir is lean/, would name
# them X, so `import Erdos634.X` does not resolve under a plain `lake build`. Making Lake work would
# mean moving every module into lean/Erdos634/ — a restructuring, not a config tweak. Until then this
# script is the end-to-end check.
#
# Usage:  bash lean/check-all.sh          (sequential; safe to run alongside the search engines)
#
# The project holds no Mathlib build of its own; LEAN_PATH is borrowed from a project that does.
set -u
cd "$(dirname "$0")/.."
MATHLIB_PROJECT="${MATHLIB_PROJECT:-$HOME/Documents/elvec1o/THREEGAP-LEAN}"
LP="$(cd "$MATHLIB_PROJECT" && lake env printenv LEAN_PATH)" || { echo "cannot get LEAN_PATH"; exit 1; }
export LEAN_PATH="$LP:$PWD/build"
mkdir -p build/Erdos634
fails=0; oks=0
for pass in 1 2; do          # two passes so the four inter-module imports resolve
  for f in lean/*.lean; do
    m=$(basename "$f" .lean)
    [ "$pass" = 2 ] && [ -f "build/Erdos634/$m.olean" ] && continue
    out=$(lean --root=. "$f" -o "build/Erdos634/$m.olean" 2>&1)
    if echo "$out" | grep -qE '^lean/.*error'; then
      echo "FAIL $m"; echo "$out" | grep -E '^lean/.*error' | head -3; fails=$((fails+1))
    else
      [ "$pass" = 1 ] && oks=$((oks+1))
    fi
  done
done
echo "---"
echo "$oks modules ok, $fails failed"
echo "sorry check (all hits should be prose in comments):"
grep -rn '\bsorry\b' lean/*.lean | sed 's/:.*/  (check by eye)/' | sort -u
exit $fails
