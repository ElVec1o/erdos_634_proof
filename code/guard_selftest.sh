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
# must ALLOW (exit 0) -- the one open row.  If this fails the guard is over-refusing.
chk 0 "OPEN basebeta N=83 (5,6)" "private/inst/i83.txt"
[ "$fail" = 0 ] && echo "guard self-test: PASS" || { echo "guard self-test: FAIL"; exit 1; }
