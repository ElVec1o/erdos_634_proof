#!/usr/bin/env bash
# guard_run.sh -- THE ONLY SANCTIONED WAY TO LAUNCH A SEARCH ENGINE ON THIS PROJECT.
#
#   code/guard_run.sh <engine-binary> FILE:<instance> [engine args...]
#
# Reads the instance, computes its identity, and REFUSES to run if that instance is
# already settled in data/SETTLED.tsv.  Exit 3 = refused as a rediscovery.
#
# Why this exists (2026-09-06): on one day six settled instances were recomputed for
# ~20 core-hours -- N=66 twice, N=59, N=107, N=62.  In the worst case the agent had
# quoted the settled-instances table VERBATIM in its own audit block and launched three
# of its rows anyway.  A rule an agent can recite is not a control.  This is a control:
# it sits on the path to the action and returns non-zero.
#
# Override (must be justified in writing, and is logged):
#   NOVELTY_OVERRIDE="reason" code/guard_run.sh ...
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REG="$ROOT/data/SETTLED.tsv"

[ $# -ge 2 ] || { echo "usage: guard_run.sh <engine> FILE:<instance> [args...]" >&2; exit 2; }
ENGINE="$1"; shift
SPEC="$1"; shift
INST="${SPEC#FILE:}"
[ -r "$INST" ] || { echo "guard: cannot read instance '$INST'" >&2; exit 2; }
[ -r "$REG"  ] || { echo "guard: registry $REG missing -- refusing to run blind" >&2; exit 2; }

# Parse by TOKEN, not by line.  Both instance formats -- multi-line (i*.txt) and packed
# one-line (fp*.txt, the format of every N=83/N=131 run) -- carry the same token stream:
#   D, a b c, 18 tile-vertex coords, 3 misc, N, ...   (N is token 26)
# The old line-based parse read "WALKS" as the tile and "1" as N on packed files, so the
# guard said NOVEL on fp59/fp66/fp107 (all settled) -- found by the 2026-09-12 data audit.
TOKS="$(awk 'BEGIN{RS="[ \t\r\n]+"} $0=="WALKS"||$0=="CORNERS"||$0=="CORNERS2"{exit} {print}' "$INST" | head -26 | tr '\n' ' ')"
set -- $TOKS
if [ $# -ge 26 ]; then
  D="$1"; TILE="$2 $3 $4"; N="${26}"
else
  TILE="$(sed -n '2p' "$INST" | tr -s ' ' | sed 's/^ *//; s/ *$//')"
  D="$(awk 'NF==1 && $1 ~ /^[0-9]+$/ {print $1; exit}' "$INST")"
  N="$(awk 'NF==1 && $1 ~ /^[0-9]+$/ {c++; if(c==2){print $1; exit}}' "$INST")"
fi
TILE_SORTED="$(echo "$TILE" | tr ' ' '\n' | sort -n | tr '\n' ' ' | sed 's/ *$//')"
[ -n "$D" ] || D="?"; [ -n "$N" ] || N="?"

printf 'guard: instance %s\n' "$INST"
printf 'guard:   D=%s  tile=(%s)  N=%s\n' "$D" "$TILE" "$N"

HIT=""
while IFS=$'\t' read -r fam e f m rn rtile verdict nodes src; do
  case "$fam" in '#'*|family) continue ;; esac
  rts="$(echo "$rtile" | tr ' ' '\n' | sort -n | tr '\n' ' ' | sed 's/ *$//')"
  if [ "$rn" = "$N" ] && [ "$rts" = "$TILE_SORTED" ]; then
    [ "$verdict" = "SEARCHING" ] && continue
    HIT="$fam (e,f,m)=($e,$f,$m) N=$rn verdict=$verdict nodes=${nodes:-n/a} :: $src"
    break
  fi
done < "$REG"

if [ -n "$HIT" ]; then
  echo "guard: ==================== REFUSED ====================" >&2
  echo "guard: THIS INSTANCE IS ALREADY SETTLED." >&2
  echo "guard:   $HIT" >&2
  if [ -n "${NOVELTY_OVERRIDE:-}" ]; then
    echo "guard: OVERRIDE ACCEPTED: $NOVELTY_OVERRIDE" >&2
    printf '%s\tOVERRIDE\t%s\t%s\n' "$(date -u +%FT%TZ)" "$INST" "$NOVELTY_OVERRIDE" >> "$ROOT/private/guard.log" 2>/dev/null || true
  else
    echo "guard: Recomputing it produces nothing. Read the source above instead." >&2
    echo "guard: If you genuinely must re-run, set NOVELTY_OVERRIDE=\"reason\"." >&2
    printf '%s\tREFUSED\t%s\t%s\n' "$(date -u +%FT%TZ)" "$INST" "$HIT" >> "$ROOT/private/guard.log" 2>/dev/null || true
    exit 3
  fi
else
  echo "guard: not in registry -- NOVEL, proceeding."
fi

# Alias warning: same (N, tile) under other filenames.  Same target, possibly different
# WALKS/CORNERS riders -- so this WARNS, it does not refuse.  Check before you assume novelty.
ALIDX="$ROOT/data/INSTANCE_ALIASES.tsv"
if [ -r "$ALIDX" ]; then
  AL="$(awk -F'\t' -v n="$N" -v t="$TILE_SORTED" 'NR>1 && $1==n && $2==t {print $3}' "$ALIDX")"
  if [ -n "$AL" ] && [ "$AL" != "${INST#$ROOT/}" ]; then
    echo "guard: NOTE this target (N=$N, tile=$TILE) also exists as:" >&2
    echo "guard:   $AL" >&2
    echo "guard:   Same target; riders may differ. Confirm yours is not already run." >&2
  fi
fi

# Rule 8: long jobs need a cap and a checkpoint.  Warn loudly if absent.
case " $* " in *" "[0-9]*) ;; *) echo "guard: WARNING no node cap given (Rule 8: cap + checkpoint + progress)." >&2 ;; esac
exec "$ENGINE" "FILE:$INST" "$@"
