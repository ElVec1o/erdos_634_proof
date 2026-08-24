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
# Usage:  code/staleness_check.sh              # audit every staleness claim in the corpus
#         code/staleness_check.sh <name>       # check one declaration before citing it as open
#         code/staleness_check.sh --blockers   # list every blocker/scope claim by age (git blame),
#                                              # flagging any that carries no date stamp
#
# WHY --blockers EXISTS.  On the same day the name-matching audit was written, it MISSED a stale
# blocker of my own: StripRigid named its remaining step in PROSE ("that planar intersection
# step") without naming the declaration that later proved it, so no name matched.  Name-matching
# is a backstop; the primary defence is R1 plus dating every claim so its age is visible.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN="$ROOT/lean/Erdos634"
KEYWORDS='is (still )?(open|carried|assumed)|remains open|not available|not formalizable|is not proved|NOT proved|cannot be (proved|expressed)|Mathlib (has no|cannot|does not)|blocker'

proved_names() { grep -rhoE "^(theorem|lemma|def) +[A-Za-z0-9_'.]+" "$LEAN"/*.lean | awk '{print $2}' | sort -u; }

if [ "${1:-}" = "--blockers" ]; then
  echo "=============================================================="
  echo "BLOCKER / SCOPE CLAIMS BY AGE  (oldest first)"
  echo "A claim older than the work around it is a re-read candidate, whether or not"
  echo "it names a declaration.  Undated claims are flagged: date them (R1)."
  echo "=============================================================="
  undated=0; total=0
  while IFS= read -r line; do
    file="${line%%:*}"; rest="${line#*:}"; lno="${rest%%:*}"; text="${rest#*:}"
    total=$((total+1))
    when="$(cd "$ROOT" && git blame -L "$lno,$lno" --date=short -- "$file" 2>/dev/null \
            | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2}' | head -1)"
    [ -z "$when" ] && when="uncommitted"
    if printf '%s' "$text" | grep -qE '[0-9]{4}-[0-9]{2}-[0-9]{2}'; then dated="dated"; else dated="UNDATED"; undated=$((undated+1)); fi
    printf '%s\t%s\t%s:%s\t%s\n' "$when" "$dated" "${file#$ROOT/}" "$lno" "$(printf '%s' "$text" | cut -c1-78)"
  done < <(grep -rnE "$KEYWORDS" "$LEAN"/*.lean 2>/dev/null | grep -vE ":[0-9]+:(theorem|lemma|def|structure)") \
    | sort | awk -F'\t' '{printf "  %-12s %-8s %-42s %s\n", $1, $2, $3, $4}'
  echo ""
  echo "=============================================================="
  echo "$total blocker/scope claims; $undated carry NO date stamp."
  echo "R1: never append a status update without editing what it falsifies."
  echo "Date every blocker so its age is visible to the next reader (including you)."
  echo "=============================================================="
  exit 0
fi

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
