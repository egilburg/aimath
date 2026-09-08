#!/bin/sh
set -eu
export LAKE_ARTIFACT_CACHE=false
cd "$(dirname "$0")"
old_lean=""
if [ "$#" -gt 0 ]; then
  if [ "$#" -ne 2 ] || [ "$1" != "--compare" ]; then
    echo "Usage: ./verify.sh [--compare OLD_LEAN_DIRECTORY]" >&2
    exit 2
  fi
  old_lean=$(cd "$2" && pwd)
fi
mkdir -p ../recheck
lean --version > ../recheck/lean-version.txt
lake build Publication > ../recheck/build.log 2>&1
lake env lean Audit.lean > ../recheck/axioms_and_statements.txt 2>&1
python3 - <<'PY'
import re
from pathlib import Path
s=Path('../recheck/axioms_and_statements.txt').read_text()
groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',s)
expected=sum(1 for x in Path('Audit.lean').read_text().splitlines() if x.startswith('#print axioms '))
assert len(groups)==expected, (len(groups),expected)
for g in groups:
    assert {x.strip() for x in g.split(',')} <= {'propext','Classical.choice','Quot.sound'}, g
assert 'sorryAx' not in s
print('Build succeeded; all',expected,'endpoint axiom lists use only the permitted standard axioms.')
PY
if [ -n "$old_lean" ]; then
  if [ ! -f "$old_lean/.lake/build/lib/lean/SierpinskiFormal/SoficSharpProcess.olean" ]; then
    echo "Build the previous public Lean package before running --compare." >&2
    exit 2
  fi
  lake env sh -c 'LEAN_PATH="$1/.lake/build/lib/lean:$LEAN_PATH"; export LEAN_PATH; lean ../verification/SemanticComparison.lean' sh "$old_lean" \
    > ../recheck/semantic_comparison.log 2>&1
  echo "Historical endpoint and definition comparison succeeded."
fi
