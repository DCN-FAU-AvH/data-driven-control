#!/usr/bin/env bash
# Check single Lean files without exceeding the machine's memory budget:
#
#   scripts/check.sh DataDrivenControl/Foo/Bar.lean [more files...]
#
# Runs `lake env lean` while holding a slot (scripts/slot.sh), so that concurrent checks never
# start more than LEAN_SLOTS Lean processes.  It writes no .olean files: imports come from the
# last `scripts/build.sh`.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
rc=0
for f in "$@"; do
  scripts/slot.sh timeout "${LEAN_TIMEOUT:-1800}" lake env lean -DautoImplicit=false -Dpp.unicode.fun=true "$f" || rc=$?
done
exit "$rc"
