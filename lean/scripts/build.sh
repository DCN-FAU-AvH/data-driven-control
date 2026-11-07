#!/usr/bin/env bash
# Sequential build: compile the library one module at a time, in import order, so that at most
# one Lean process (plus any check.sh slots) runs at once.  A plain `lake build` starts every
# ready module in parallel and swaps on a machine with ~11 GB of memory.
#
#   scripts/build.sh            # all modules imported by DataDrivenControl.lean
#   scripts/build.sh Mod.Name   # just this module (and, sequentially, its missing deps)
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
# One build at a time (concurrent `lake build`s would race on shared .olean files).
exec 8>.lake/build.lock; flock 8
python3 - "$@" <<'PY' > .lake/build-order.txt
import re, sys, pathlib
root = pathlib.Path('.')
def deps(mod):
    p = root / (mod.replace('.', '/') + '.lean')
    if not p.exists(): return []
    return [m for m in re.findall(r'^(?:public\s+)?import\s+(\S+)', p.read_text(), re.M)
            if m.startswith('DataDrivenControl')]
targets = sys.argv[1:] or deps('DataDrivenControl')
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps(m): visit(d)
    order.append(m)
for t in targets: visit(t)
print('\n'.join(order))
PY
fail=0
while read -r m; do
  out=$(scripts/slot.sh lake build "$m" 2>&1); rc=$?
  if [ $rc -ne 0 ]; then echo "FAIL $m"; echo "$out" | grep -E 'error' | head -20; fail=1
  else n=$(echo "$out" | grep -c "declaration uses 'sorry'"); if [ "$n" -gt 0 ]; then echo "ok   $m (sorry decls: $n)"; else echo "ok   $m"; fi; fi
done < .lake/build-order.txt
[ $# -eq 0 ] && [ $fail -eq 0 ] && scripts/slot.sh lake build DataDrivenControl 2>&1 | tail -1
exit $fail
