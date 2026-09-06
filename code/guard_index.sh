#!/usr/bin/env bash
# guard_index.sh -- rebuild data/INSTANCE_ALIASES.tsv, the (N,tile) -> files index.
# Catches the "same instance under two filenames" rediscovery vector
# (cev62.txt and cevm1_6_7.txt were the same problem; nobody noticed for weeks).
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/data/INSTANCE_ALIASES.tsv"
{ printf 'N\ttile\tfiles\n'
  find "$ROOT/private/inst" "$ROOT/private/ROOM" -name '*.txt' 2>/dev/null | while read -r f; do
    n="$(awk 'NF==1 && $1 ~ /^[0-9]+$/ {c++; if(c==2){print $1; exit}}' "$f" 2>/dev/null)"
    t="$(sed -n '2p' "$f" 2>/dev/null | tr -s ' ' | sed 's/^ *//;s/ *$//')"
    case "$t" in ''|*[!0-9\ ]*) continue ;; esac
    [ -n "$n" ] || continue
    ts="$(echo "$t" | tr ' ' '\n' | sort -n | tr '\n' ' ' | sed 's/ *$//')"
    printf '%s\t%s\t%s\n' "$n" "$ts" "${f#$ROOT/}"
  done | sort -n | awk -F'\t' '{k=$1"\t"$2; if(k==p){acc=acc","$3} else {if(p!="")print p"\t"acc; p=k; acc=$3}} END{if(p!="")print p"\t"acc}'
} > "$OUT"
echo "wrote $OUT ($(($(wc -l < "$OUT")-1)) distinct instances)"
awk -F'\t' 'NR>1 && $3 ~ /,/ {print "  ALIASES  N="$1"  tile=("$2")  ->  "$3}' "$OUT"
