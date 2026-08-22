#!/usr/bin/env bash
# novelty_check.sh -- MANDATORY before formalizing or claiming any new result.
#
# Searches the whole corpus for a statement before it is written again:
#   lean/Erdos634/*.lean   declaration names AND docstrings
#   paper/*.tex            labels, theorem/lemma/remark statements
#   private/RESEARCH_LOG.md  logged dead ends and retractions
#
# Usage:  code/novelty_check.sh <term> [term ...]
# Exit 1 if ANY term matches anywhere -- treat that as "already known, go read it".
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
hits=0
for term in "$@"; do
  echo "=============================================================="
  echo "TERM: $term"
  echo "--- Lean declaration names ---"
  grep -rniE "^(theorem|lemma|def|structure) +[A-Za-z0-9_']*${term}" "$ROOT/lean/Erdos634" 2>/dev/null | head -8 && hits=1
  echo "--- Lean docstrings / comments ---"
  grep -rniE "$term" "$ROOT/lean/Erdos634"/*.lean 2>/dev/null | grep -vE "^[^:]*:[0-9]+:(theorem|lemma|def|structure)" | head -8 && hits=1
  echo "--- paper (labels and prose) ---"
  grep -rniE "$term" "$ROOT/paper"/*.tex 2>/dev/null | head -8 && hits=1
  echo "--- research log (dead ends, retractions) ---"
  grep -niE "$term" "$ROOT/private/RESEARCH_LOG.md" 2>/dev/null | head -6 && hits=1
done
echo "=============================================================="
if [ "$hits" -eq 1 ]; then
  echo "MATCHES FOUND -- read them before writing anything. Presume the result exists."
  exit 1
fi
echo "no matches -- but also run a literature search (Rule 4) before claiming novelty."
exit 0
