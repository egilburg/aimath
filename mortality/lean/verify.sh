#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LAKE_ARTIFACT_CACHE=false
mkdir -p ../verification
# An empty local project build is required; public dependency caches may be reused.
if [ -d .lake/build ]; then
  echo 'Refusing to reuse project artifacts: move or remove lean/.lake/build first.' >&2
  exit 1
fi
lake build Publication > ../verification/build.log 2>&1
lake env lean Specification.lean > ../verification/specification.log 2>&1
lake env lean Audit.lean > ../verification/axioms_and_statements.txt 2>&1
lean --version > ../verification/lean-version.txt
printf 'PASS: fresh project build, exact specifications and endpoint audits.\n'
