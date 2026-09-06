#!/usr/bin/env bash
# guard_record.sh -- append a COMPLETED verdict to data/SETTLED.tsv.
#   code/guard_record.sh <family> <e> <f> <m> <N> "<tile>" <verdict> <nodes> "<source>"
# verdict in: NO_TILING | TILING_EXISTS | SEARCHING
# Run this the moment a search terminates.  A result that is not recorded here WILL be
# recomputed by someone -- that is exactly what happened on 2026-09-06.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; REG="$ROOT/data/SETTLED.tsv"
[ $# -eq 9 ] || { echo "usage: guard_record.sh <family> <e> <f> <m> <N> \"<tile>\" <verdict> <nodes> \"<source>\"" >&2; exit 2; }
case "$7" in NO_TILING|TILING_EXISTS|SEARCHING) ;; *) echo "bad verdict '$7'" >&2; exit 2 ;; esac
if awk -F'\t' -v n="$5" -v t="$6" 'NR>2 && $5==n && $6==t {found=1} END{exit !found}' "$REG"; then
  echo "guard_record: N=$5 tile=($6) already in registry -- not duplicating. Edit by hand if the verdict changed." >&2
  exit 1
fi
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$7" "$8" "$9" >> "$REG"
echo "guard_record: recorded $1 (e,f,m)=($2,$3,$4) N=$5 verdict=$7"
