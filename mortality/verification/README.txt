VERIFICATION OF REVISION 2026-09-08-r2

This supplement verifies the extracted FiniteMonoidMortality development. The earlier
r1 master-library build is not used as a substitute for these new checks.

RESULTS
Fresh build from empty project output with LAKE_ARTIFACT_CACHE=false: exit 0.
Exact endpoint statement and transitive-axiom audit: exit 0.
Statement/definition preservation checks against the earlier proof: passed.
All advertised endpoints use only propext, Classical.choice and Quot.sound.
The package contains 7 mathematical modules, all reachable from Publication.

PROVENANCE AND REPLAY
PROVENANCE.json records exact checks, original proof source, counts and scope.
ENVIRONMENT.json and VERIFICATION_ENVIRONMENT.txt identify the actual compiler,
dependency revisions, cache/source-build provenance and runtime compatibility wrapper.
source_closure.json records the current module graph and hashes.
SHA256SUMS covers the current lean/ and verification/ files, except itself.
From the package root, run sha256sum -c verification/SHA256SUMS.
Then follow ../README.txt and ../lean/README.txt to run sh verify.sh in lean/.
Fresh replay output goes to recheck/, preserving the recorded successful logs.

READING THE PROOF
REFACTOR.txt explains the mathematical module sequence and the extraction.
REFACTOR_MAP.json maps retained declarations to the earlier source.
CLAIM_MAP.txt connects the manuscript to current Lean declarations and separates
exposition-level bridges from separately named formal endpoints.
The manuscript retains the main mathematical arguments directly.

COMPATIBILITY
specification.log records three kernel-checked compatibility theorems from
lean/Specification.lean, using the original endpoint statements and transparent
matrixWord/finiteMortalityBound definitions. verify.sh runs this check normally.
source_equivalence.json and check_source_equivalence.py record a supplementary
comparison of retained declaration source bodies. REPRODUCE_EXTRACTION.txt explains
the optional source extraction audit using the publicly available earlier package.

These checks concern formal mathematical statements and their specified assumptions.
They do not establish global priority or constitute professional human review.
The build logs retain ordinary linter warnings. No error or unproved project axiom
supports the advertised endpoints. Historical research records are retained privately;
they are not required to read or build this paper's current proof.
