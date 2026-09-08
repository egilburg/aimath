#!/bin/sh
set -eu
cd "$(dirname "$0")"
export LAKE_ARTIFACT_CACHE=false
mkdir -p ../recheck
lean --version > ../recheck/lean-version.txt
lake build Publication > ../recheck/build.log 2>&1
lake env lean Audit.lean > ../recheck/axioms_and_statements.txt 2>&1
lake env lean Specification.lean > ../recheck/specification.log 2>&1
python3 - <<'PY'
import re
from pathlib import Path
for source, output in [('Audit.lean', 'axioms_and_statements.txt'),
                       ('Specification.lean', 'specification.log')]:
    s = (Path('../recheck') / output).read_text()
    groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', s)
    expected = sum(line.startswith('#print axioms ') for line in Path(source).read_text().splitlines())
    assert len(groups) == expected, (source, len(groups), expected)
    for g in groups:
        assert {x.strip() for x in g.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}, g
    assert 'sorryAx' not in s
    print(source, ':', expected, 'axiom lists use only standard permitted axioms.')
print('Build, endpoint audit and original-statement compatibility checks succeeded.')
PY
