An Exponential Mortality Bound for Finite Real Matrix Monoids

https://github.com/egilburg/aimath

Public release: 2026-09-08-r1 (8 September 2026).
Manuscript: exponential_mortality_bound_for_finite_real_matrix_monoids.pdf
Editable source: exponential_mortality_bound_for_finite_real_matrix_monoids.tex, preamble.tex, disclosure.tex,
and bibliography.bib. The link above identifies this source without an author
or role designation. Citation details: citation.bib.

RESULT
For n > 0, any family of real n × n matrices whose entire word-product monoid is finite and contains zero has a zero word of length at most b(n) = 2^(n−1) + (2^(n−1)−1)n(n+1)/2. The same dimension and word bound hold over the rationals. No finite-alphabet assumption is needed.

REPRODUCE THE PROOF
Install Git, Python 3 and Elan (https://github.com/leanprover/elan).
From this package directory:

    cd lean
    elan toolchain install leanprover/lean4:v4.33.1
    lake exe cache get
    sh verify.sh

The optional cache command retrieves public dependency artifacts. The pinned
lake-manifest.json must be retained; do not update dependency versions during
reproduction. verify.sh builds Publication.lean and prints Audit.lean statements
and transitive axioms to ../recheck/. That output is generated locally.

Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The complete project-local import closure is included (102 modules).
The source and configuration match the successfully built proof package.
Its three advertised endpoints were audited with only propext, Classical.choice
and Quot.sound. This export changes no Lean module or build configuration.
The verification/ supplement includes the successful build log, exact statement and
axiom audit, proof-source provenance, manuscript correspondence and SHA256SUMS.
Research-development records are not part of the public payload.
PUBLICATION.json lists the actual public payload and source hashes.

REBUILD THE MANUSCRIPT
With TeX Live and latexmk installed, run:

    sh build_manuscript.sh

The rebuilt PDF appears in recheck/tex. Public-export edits only reconcile
references to attachments that are not distributed; mathematical claims and
proof text are retained. Read the paper's formal-scope qualifications.

STATUS, LICENSE AND CORRECTIONS
Self-published; no professional human mathematical review is claimed. Original
mathematical contribution and exposition were produced by AI, with prior work
separately credited. The full AI/vendor/model and as-is disclosure appears above
the manuscript references. Independent verification is necessary as appropriate;
Lean verification does not establish global novelty or validate every prose claim.

LICENSE.txt contains the full CC-BY-4.0 legal code for rights that can be granted.
Third-party terms are preserved in third_party_licenses/; see
THIRD_PARTY_NOTICES.txt. Mathematical facts and ideas are not made proprietary.

Report corrections at https://github.com/egilburg/aimath/issues using the Correction report form.
See CORRECTIONS.txt and the repository RELEASES.txt. Cite the version and a
permanent commit URL; the main-branch URL is the current copy, not an immutable
identifier. No DOI is assigned. No response time or professional review service
is promised.
