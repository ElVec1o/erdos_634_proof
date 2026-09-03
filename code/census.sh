#!/bin/sh
# Rule-0 census for Erdos #634.
# Authoritative source: the \lab{...} tags in paper/*.tex, one per tracked statement.
# A tag may carry a qualifier after the leading word ("PROVED: the arithmetic VERIFIED");
# only the LEADING word is the statement's label, so we cut at the first ':' or space.
cd "$(dirname "$0")/.." || exit 1
grep -ho '\\lab{[^}]*}' paper/*.tex \
  | sed 's/\\lab{//; s/}$//' \
  | sed 's/[:,;[:space:]].*//' \
  | sort | uniq -c | sort -rn
echo "---"
printf 'total tagged statements: '
grep -ho '\\lab{[^}]*}' paper/*.tex | wc -l | tr -d ' '
