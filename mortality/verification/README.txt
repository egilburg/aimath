# Verification of this exact package — 8 September 2026

Source input `6372f85822ed9d035df4919de385ac2a79170930`. No project Lean source was changed: every copied source Git blob was compared with the pinned remote inventory, and SHA-256 values are in source_closure.json. Source and configuration checksums are in SHA256SUMS (paths relative to the package root).

## Exported Lean build and endpoint audit

The actual exported project started with an empty .lake/build directory. Its .lake/packages directory pointed only to the pinned public dependency installations/caches; no prebuilt project-local module was copied. Commands run from this package's lean/ directory:

```sh
lake build Publication > ../verification/build.log 2>&1
lake env lean Audit.lean > ../verification/axioms_and_statements.txt 2>&1
```

Both commands returned **exit status 0**. There were **102 compiled project-local modules**, matching the full packaged source closure; Publication.olean was produced in this build. No reliable Lake aggregate job count was retained for this build; the successful exit and compiled closure were checked directly. All 3 endpoint axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`; no sorryAx or unproved project axiom supports them. Exact types and proof expressions are retained in the audit output. Deprecation/style warnings in the build logs are not suppressed or presented as proof errors.

Environment: Linux x86_64, official Lean 4.33.1 compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; other exact revisions in lean/lake-manifest.json. Public dependency caches were reused, not rebuilt from their foundational sources.

This runtime required `LD_PRELOAD` with an own-process executable-path wrapper because the compiler initially could not locate its application through /proc/<pid>/exe. The source is `runtime-self-exe.c`: it redirects only that own-process readlink to /proc/self/exe. It does not alter Lean source, kernel, proof terms or axioms. The actual run set PATH to the official compiler bin directory and LD_PRELOAD to the compiled wrapper. On a similarly affected Linux runtime it can be compiled with `cc -shared -fPIC runtime-self-exe.c -ldl -o self-exe.so`; set LD_PRELOAD to its absolute path. Normal Elan installations do not need this workaround. The binary wrapper is not included.


REPRODUCTION AND SCOPE
From the package root, run sha256sum -c verification/SHA256SUMS.
Then follow ../README.txt to install the pinned toolchain and run lean/verify.sh.
CLAIM_MAP.txt maps manuscript claims to formal declarations; axioms_and_statements.txt retains exact types and transitive axioms.
This editorial republication changed no Lean source or build configuration. The successful original build and audit are retained, not represented as a new run. These checks are not professional human review and do not establish historical priority.
