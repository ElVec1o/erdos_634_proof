#!/usr/bin/env bash
# Build the Erdos634 Lean corpus.
#
# The corpus has no Lake package of its own: Mathlib is 6.7 GB and the machine has ~25 GB free,
# so building a second copy is not acceptable (research Rule 8). Instead we borrow the LEAN_PATH
# of an existing project that already has Mathlib built, add our own build directory to it, and
# invoke `lean` directly. Files with no project imports compile in any order; files that import
# other project modules must come after them in DEPS below.
#
# Usage:  code/build_lean.sh [/path/to/project/with/mathlib]
set -euo pipefail

MATHLIB_PROJECT="${1:-$HOME/Documents/elvec1o/THREEGAP-LEAN}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="$ROOT/build"

if [ ! -d "$MATHLIB_PROJECT" ]; then
  echo "error: no Mathlib project at $MATHLIB_PROJECT" >&2; exit 1
fi

LP="$(cd "$MATHLIB_PROJECT" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$LP:$BUILD"
mkdir -p "$BUILD/Erdos634"

# Modules that other project files import, in dependency order.
DEPS=(SectorArea Wedge OrderForcing SupportFace)
for m in "${DEPS[@]}"; do
  echo "  olean  $m"
  lean -o "$BUILD/Erdos634/$m.olean" "$ROOT/lean/$m.lean"
done

# Everything else: type-check only.
fail=0
for f in "$ROOT"/lean/*.lean; do
  base="$(basename "$f" .lean)"
  printf '  check  %-24s' "$base"
  if out="$(lean "$f" 2>&1)"; then
    if echo "$out" | grep -q "declaration uses 'sorry'"; then echo "SORRY"; fail=1; else echo "ok"; fi
  else
    echo "FAIL"; echo "$out" | head -5; fail=1
  fi
done
exit $fail
