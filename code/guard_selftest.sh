#!/usr/bin/env bash
# guard_selftest.sh -- BOTH-DIRECTION regression for guard_run.sh.
# Mode E says a guard that refuses everything is as broken as one that refuses nothing,
# so this asserts refusals AND an allowance.  Run after every edit to the guard or registry.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
fail=0
chk() { # chk <want> <label> <instance>
  local want="$1" label="$2" inst="$3" got
  [ -r "$inst" ] || { printf '  SKIP %-34s (missing %s)\n' "$label" "$inst"; return; }
  code/guard_run.sh /bin/echo "FILE:$inst" >/dev/null 2>&1
  got=$?
  if [ "$got" = "$want" ]; then printf '  ok   %-34s exit=%s\n' "$label" "$got"
  else printf '  FAIL %-34s exit=%s want=%s\n' "$label" "$got" "$want"; fail=1; fi
}
echo "guard self-test:"
# must REFUSE (exit 3) -- the instances actually burned on 2026-09-06
for n in 11 23 26 39 47 59 66 71 74 107; do chk 3 "settled basebeta N=$n" "private/inst/i$n.txt"; done
# must REFUSE (exit 3) -- the same instances in the PACKED one-line format (fp*.txt).  The
# 2026-09-12 data audit found the guard said NOVEL on these: it parsed by line, and a packed
# file has "WALKS" on line 2.  Every N=83/N=131 run used this format.
for n in 11 59 66 107; do chk 3 "settled basebeta N=$n (packed)" "private/inst/fp$n.txt"; done
# must ALLOW (exit 0) -- the one open row.  If this fails the guard is over-refusing.
chk 0 "OPEN basebeta N=83 (5,6)" "private/inst/i83.txt"
chk 0 "OPEN basebeta N=83 (5,6) (packed)" "private/inst/fp83.txt"
# must PASS THE ENGINE ARGS THROUGH -- on 2026-09-12 a parse edit clobbered "$@" and 21 sweep
# words ran with a node cap of D=2303 instead of 50M, all returning INCONCLUSIVE in seconds.
out="$(code/guard_run.sh /bin/echo "FILE:private/inst/i83.txt" 424242 2>/dev/null)"
case "$out" in *" 424242") printf '  ok   %-34s\n' "engine args pass through" ;;
  *) printf '  FAIL %-34s got: %s\n' "engine args pass through" "$out"; fail=1 ;; esac
[ "$fail" = 0 ] && echo "guard self-test: PASS" || { echo "guard self-test: FAIL"; exit 1; }
