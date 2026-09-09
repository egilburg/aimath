VERIFICATION OF REVISION 2026-09-08-r2

This supplement verifies the extracted SoficMarkovOrder development. The recorded build and audits apply to the current
proof sources; this documentation cleanup does not claim a new build.

RESULTS
Fresh build from empty project output with LAKE_ARTIFACT_CACHE=false: exit 0.
Exact endpoint statement and transitive-axiom audit: exit 0.
Statement/definition preservation checks against the earlier proof: passed.
All advertised endpoints use only propext, Classical.choice and Quot.sound.
The package contains 21 mathematical modules, all reachable from Publication.

PROVENANCE AND REPLAY
PROVENANCE.json records exact checks, original proof source, counts and scope.
ENVIRONMENT.json and VERIFICATION_ENVIRONMENT.txt identify the actual compiler,
dependency revisions, cache/source-build provenance and runtime compatibility wrapper.
source_closure.json records the current module graph and hashes.
SHA256SUMS covers the current lean/ and verification/ files, except itself.
From the package root, run sha256sum -c verification/SHA256SUMS.
From the package root, follow README.txt and lean/README.txt to run
sh verify.sh in lean/.
Fresh replay output goes to recheck/, preserving the recorded successful logs.

READING THE PROOF
REFACTOR.txt explains the mathematical module sequence and the extraction.
REFACTOR_MAP.json maps retained declarations to the earlier source.
CLAIM_MAP.txt connects the manuscript to current Lean declarations and separates
exposition-level bridges from separately named formal endpoints.
The manuscript retains the main mathematical arguments directly.

COMPATIBILITY
semantic_comparison.log records exact compiled-expression equality for four
endpoint types and their custom type/definition/constructor closure (21 declarations,
including the endpoints), under the explicit naming map. SemanticComparison.lean
is the included executable check; the earlier public proof is an external input
only for the optional --compare mode of verify.sh. It is not a dependency of the
current proof build. source_comparison.py/json provide a supplementary source check.

These checks concern formal mathematical statements and their specified assumptions.
They do not establish global priority or constitute professional human review.
The build logs retain ordinary linter warnings. No error or unproved project axiom
supports the advertised endpoints. The current proof builds from this package and its pinned public dependencies.
