Verification — 2026-09-10-r3

The extracted project was rebuilt from an empty project .lake/build with LAKE_ARTIFACT_CACHE=false. All 25 local mathematical modules compiled; lake reported 2329 jobs including pinned public dependencies. Specification.lean kernel-checks 20 exact source statements under the identifier mapping. Audit.lean checks endpoint types and transitive axioms, including three additional helper lemmas. Only propext, Classical.choice and Quot.sound occur. No sorry/admit or project axiom is present.

Use lean/verify.sh for independent reproduction on a standard Lean 4.33.1 installation. Install the pinned public dependencies; do not reuse this project's compiled outputs. Actual successful logs: build.log, specification.log, axioms_and_statements.txt, lean-version.txt. The environment adaptation used here is described in VERIFICATION_ENVIRONMENT.txt and runtime-self-exe.c; it affects locating the compiler executable, not the proof kernel.

CLAIM_MAP.txt distinguishes formal endpoints from elementary scalar-extension/representation interpretations and historical comparisons. The manuscript uses an explicit invariant flag and explicit integer examples, not an unformalized general composition-series construction. The SLP theorem asserts small witness existence and correct evaluation.

PUBLICATION.json identifies the distributed files; SHA256SUMS binds their bytes.
PROVENANCE.json and ENVIRONMENT.json describe the recorded check and environment.
