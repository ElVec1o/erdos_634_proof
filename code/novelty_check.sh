#!/usr/bin/env bash
# novelty_check.sh -- MANDATORY before formalizing or claiming any new result.
#
# Searches the whole corpus for a statement before it is written again:
#   lean/Erdos634/*.lean     declaration names AND docstrings
#   paper/*.tex              labels, theorem/lemma/remark statements
#   private/RESEARCH_LOG.md  logged dead ends and retractions
#
# Usage:  code/novelty_check.sh <term> [term ...]
# Exit 1 if ANY term matches anywhere -- treat that as "already known, go read it".
#
# 2026-08-23: rewritten.  The previous version piped every grep into `head`, whose exit
# status is 0 regardless of whether grep matched, so `&& hits=1` fired unconditionally and
# the script reported MATCHES FOUND on EVERY run -- including genuine novelty.  Four
# rediscoveries were committed while it was crying wolf.  Matches are now counted, never
# truncated silently, and the verdict is printed FIRST as well as last so that reading
# either end of the output is safe.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MAX=40

scan() {  # scan <label> <command...>  -> prints all matches, returns match count via $COUNT
  local label="$1"; shift
  local out; out="$("$@" 2>/dev/null || true)"
  local n=0
  [ -n "$out" ] && n=$(printf '%s\n' "$out" | wc -l | tr -d ' ')
  COUNT=$n
  if [ "$n" -eq 0 ]; then
    printf '  %-32s none\n' "$label"
  else
    printf '  %-32s %s match(es)\n' "$label" "$n"
    printf '%s\n' "$out" | head -"$MAX" | sed 's|^'"$ROOT"'/||; s/^/      /'
    [ "$n" -gt "$MAX" ] && printf '      ... %s further match(es) NOT SHOWN -- narrow the term\n' "$((n - MAX))"
  fi
}

BODY=""; TOTAL=0; SUMMARY=""
for term in "$@"; do
  t=0
  section="$(
    echo "=============================================================="
    echo "TERM: $term"
    scan "Lean declaration names" grep -rniE "^(theorem|lemma|def|structure) +[A-Za-z0-9_']*${term}" "$ROOT/lean/Erdos634"; a=$COUNT
    scan "Lean docstrings / comments" bash -c "grep -rniE \"\$1\" \"\$2\"/*.lean | grep -vE '^[^:]*:[0-9]+:(theorem|lemma|def|structure)'" _ "$term" "$ROOT/lean/Erdos634"; b=$COUNT
    scan "paper (labels and prose)" bash -c "grep -rniE \"\$1\" \"\$2\"/*.tex" _ "$term" "$ROOT/paper"; c=$COUNT
    scan "research log" grep -niE "$term" "$ROOT/private/RESEARCH_LOG.md"; d=$COUNT
    echo "TERMTOTAL $((a+b+c+d))"
  )"
  t=$(printf '%s\n' "$section" | sed -n 's/^TERMTOTAL //p')
  section="$(printf '%s\n' "$section" | grep -v '^TERMTOTAL ')"
  BODY="${BODY}${section}"$'\n'
  TOTAL=$((TOTAL + t))
  if [ "$t" -gt 0 ]; then SUMMARY="${SUMMARY}  HIT   ${term}  (${t})"$'\n'
  else SUMMARY="${SUMMARY}  clear ${term}"$'\n'; fi
done

echo "=============================================================="
if [ "$TOTAL" -gt 0 ]; then
  echo "VERDICT: $TOTAL MATCH(ES). READ THEM BELOW BEFORE WRITING ANYTHING."
  echo "Presume the result exists until you have read every match and shown it does not."
else
  echo "VERDICT: no corpus matches."
fi
printf '%s' "$SUMMARY"
echo "=============================================================="
printf '%s' "$BODY"
echo "=============================================================="
if [ "$TOTAL" -gt 0 ]; then
  echo "VERDICT (repeat): $TOTAL MATCH(ES) -- read them, above."
  exit 1
fi
echo "no matches -- but also run a literature search (Rule 4) before claiming novelty."
exit 0
