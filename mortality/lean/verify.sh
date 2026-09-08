#!/bin/sh
set -eu
cd "$(dirname "$0")"
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
