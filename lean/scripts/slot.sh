#!/usr/bin/env bash
# Run a command while holding one of LEAN_SLOTS machine-wide "Lean process" slots.
# Used by check.sh and build.sh: every Lean process loads Mathlib and needs several GB of
# memory.  Waits for a free slot.
set -uo pipefail
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
# Limit: $LEAN_SLOTS, else .lake/lean-slots/limit (read on every call), else 2.
N=${LEAN_SLOTS:-$(cat "$ROOT_DIR/.lake/lean-slots/limit" 2>/dev/null || echo 2)}
LOCKDIR="$(cd "$(dirname "$0")/.." && pwd)/.lake/lean-slots"
mkdir -p "$LOCKDIR"
waited=0
while true; do
  for i in $(seq 1 "$N"); do
    exec 9>"$LOCKDIR/slot$i"
    if flock -n 9; then
      [ "$waited" -ge 30 ] && echo "[slot.sh] waited ${waited}s for a Lean slot" >&2
      "$@"; exit $?
    fi
    exec 9>&-
  done
  sleep 3; waited=$((waited + 3))
done
