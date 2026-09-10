Minimum-Rank and Mortality Bounds for Finite Real Matrix Monoids
Report revision 2026-09-10-r4 (10 September 2026).

Read exponential_mortality_bound_for_finite_real_matrix_monoids.pdf or its editable TeX source.
Build the report with bash build_report.sh. The public Lean supplement
and reproduction commands are described in lean/README.txt; see
verification/README.txt and verification/CLAIM_MAP.txt for scope and checks.

For a finite entire real matrix monoid in dimension n with minimum rank s,
a word attains s within B(n,s)=n*2^(n-s)-n(n+1)/2+s(s-1)/2 letters.
At s=0 this improves r2 from order n^2*2^n to n*2^n. R3 also includes the
sharp planar threshold four, invariant-flag bounds and exact independent small
blocks, a boundedness/individual-periodicity boundary, and cubic-size valid
compressed witness existence with evaluator correctness. It does not assert
polynomial-time synthesis or sharpness of the general bound.

Self-published; no professional human mathematical review is claimed.
The focused Lean project contains 25 mathematical modules and 194 declarations.
Its recorded clean build, 20 exact statement checks and endpoint axiom audits
passed. The source and manuscript bytes are unchanged during public transfer;
the included verification logs retain their original check date.

Edition alias mortality-r4 is pending creation. The PDF's Archived edition link
will resolve when that tag is created. Use the exact public commit link in the
repository-root RELEASES.txt in the meantime; earlier r1/r2 tags remain fixed.

Almeida–Steinberg's flag method and the classical Cerny example are credited.
A Protasov 2021 full-text comparison remains incomplete. No global priority or
unmatched best-known assertion is made. Read the manuscript's exact comparisons.

License: LICENSE.txt (CC-BY-4.0 for publisher-controlled material, to the extent
applicable rights exist). Third-party exceptions: THIRD_PARTY_NOTICES.txt.
Citation: citation.bib. Changes: CHANGES.txt. Corrections: CORRECTIONS.txt.
Source: https://github.com/egilburg/aimath
