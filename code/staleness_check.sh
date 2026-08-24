#!/usr/bin/env bash
# staleness_check.sh -- MANDATORY before citing any result as open, carried, blocked,
# unavailable, or not formalizable.
#
# WHY THIS EXISTS.  On 2026-08-24 two separate false claims were made in this project's own
# files, each by reading a docstring that had gone stale:
#   * StripRigid's blocker said the link "needs a formalization of tilings this project does
#     not have" -- Congruence.lean had supplied exactly that.
#   * StraightEdgeSums said HasAngleSums does not cover interior tiling-edge points, so a step
#     had to be carried -- HasAngleSums had been DISCHARGED on 2026-08-16, and the status note
#     saying so was sitting eight lines below a line still calling it open, in the SAME FILE.
# Both came from the same habit: appending a STATUS UPDATE instead of editing the claim it
# falsifies.  A reader (including me) hits the stale line first and stops.
#
# THE RULE, in two parts:
#   (R1) NEVER append a status update without editing every earlier line it falsifies.
#        A file must not contain a claim its own later text contradicts.
#   (R2) Before writing "X is open/carried/blocked/not available", run this script on X.
#        If X names a declaration that is proved anywhere in the corpus, the claim is stale.
#
# Usage:  code/staleness_check.sh            # audit every staleness claim in the corpus
#         code/staleness_check.sh <name>     # check one declaration before citing it as open
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN="$ROOT/lean/Erdos634"
KEYWORDS='is (still )?(open|carried|assumed)|remains open|not available|not formalizable|is not proved|NOT proved|cannot be (proved|expressed)|Mathlib (has no|cannot|does not)|blocker'

proved_names() { grep -rhoE "^(theorem|lemma|def) +[A-Za-z0-9_'.]+" "$LEAN"/*.lean | awk '{print $2}' | sort -u; }

if [ "$#" -ge 1 ]; then
  for name in "$@"; do
    echo "=============================================================="
    echo "CHECKING: $name"
    hits="$(grep -rnE "^(theorem|lemma|def) +[A-Za-z0-9_'.]*${name}" "$LEAN"/*.lean 2>/dev/null || true)"
    if [ -n "$hits" ]; then
      echo "  PROVED IN THE CORPUS -- do NOT call this open/carried:"
      printf '%s\n' "$hits" | sed "s|^$ROOT/||; s/^/      /"
    else
      echo "  no proved declaration matches -- citing it as open may be legitimate,"
      echo "  but still read any STATUS notes in the file that defines it."
    fi
  done
  exit 0
fi

echo "=============================================================="
echo "STALENESS AUDIT: every open/carried/blocked claim, with a verdict"
echo "=============================================================="
tmp="$(mktemp)"; proved_names > "$tmp"
flagged=0; total=0
while IFS= read -r line; do
  file="${line%%:*}"; rest="${line#*:}"; lno="${rest%%:*}"; text="${rest#*:}"
  case "$text" in *theorem\ *|*lemma\ *|*def\ *) ;; esac
  total=$((total+1))
  # names mentioned in backticks on this line
  names="$(printf '%s' "$text" | grep -oE '`[A-Za-z0-9_'"'"'.]+`' | tr -d '`' | sort -u || true)"
  verdict=""
  for n in $names; do
    base="${n##*.}"; [ ${#base} -lt 4 ] && continue
    if grep -qxF "$base" "$tmp" 2>/dev/null; then verdict="$verdict $n"; fi
  done
  if [ -n "$verdict" ]; then
    flagged=$((flagged+1))
    echo ""
    echo "  STALE? ${file#$ROOT/}:$lno"
    echo "     $(printf '%s' "$text" | cut -c1-100)"
    echo "     names PROVED in corpus:$verdict"
  fi
done < <(grep -rnE "$KEYWORDS" "$LEAN"/*.lean 2>/dev/null | grep -vE ":[0-9]+:(theorem|lemma|def|structure)")
rm -f "$tmp"
echo ""
echo "=============================================================="
echo "$total staleness claims scanned; $flagged mention a declaration that IS proved."
echo "A flag is not proof of staleness -- read the line.  But every one must be read."
echo "RULE R1: never append a status update without editing what it falsifies."
echo "=============================================================="
[ "$flagged" -gt 0 ] && exit 1
exit 0
