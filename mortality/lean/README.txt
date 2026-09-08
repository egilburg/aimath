FINITE MONOID MORTALITY: REBUILD AND AUDIT

This is a self-contained, paper-focused Lean source package. Its seven
mathematical modules use the namespace FiniteMonoidMortality. Publication.lean
imports Main; no parent research library is required.

Install Git and Elan from https://github.com/leanprover/elan and run here:

    elan toolchain install leanprover/lean4:v4.33.1
    lake exe cache get
    sh verify.sh

The dependency cache download is optional for correctness. Preserve the
supplied lake-manifest.json; do not run lake update to change its revisions.
The required compiler is Lean 4.33.1, official commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Mathlib is pinned at
0df444a360eaa60ab8c11dca51a86af692955474; the manifest pins all nine public
dependencies. No compiler binaries, dependency copies or project build cache
are distributed.

verify.sh disables Lake's global artifact restoration with
LAKE_ARTIFACT_CACHE=false, compiles Publication, prints the three exact endpoint statements
and transitive axiom lists using Audit.lean, and checks Specification.lean.
The latter reproduces the original published claims and the two transparent
custom definitions in their statement closure; each claim is proved directly
by the refactored endpoint. The script requires every audited theorem to
use only propext, Classical.choice and Quot.sound, and rejects sorryAx.
Fresh output is written to ../recheck/ and does not overwrite the recorded
verification supplement in ../verification/.

Reading order: MatrixWords; ReachableSpans; Compression; InvariantForms;
QuadraticObservation; Descent; Main. The first two introduce only the word
and finite-dimensional orbit operations needed by the mortality argument.
The next three construct a short trace-defect witness. Descent pays for both
outside copies of each sandwich. Main proves the real bound and its rational
specialization, without assuming a finite generator indexing type.

The retained verification supplement describes the preparation environment,
source/configuration hashes, compiler/dependency pins, successful build and
axiom output, and the theorem mapping. The compatibility shim used by the
preparation runtime is documented there; normal Elan installations do not
need it.
