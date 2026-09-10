FiniteMonoidMortality — manuscript revision 2026-09-10-r3

Install Lean 4.33.1 using elan. In lean/, run `lake exe cache get` for pinned public mathlib dependencies if desired, then `bash verify.sh` with no lean/.lake/build directory. The script disables Lake artifact restoration for this project's clean build and writes build, statement and axiom logs in ../verification. Existing pinned public dependency artifacts are permitted. The Lake manifest pins all dependency commits; no private repository is needed.

Entrypoint: Publication.lean. Exact statements: Specification.lean. Endpoint/type/axiom audit: Audit.lean. The only permitted transitive axioms are propext, Classical.choice and Quot.sound. No project axiom or admitted proof is present.

Module sequence and mathematical roles:
- MinimalRankCompression: matrix words, rank factorization, compressed returns and rank inequalities. MatrixWordScalarExtension and MatrixRankScalarExtension: field embeddings preserve products, zero and rank.
- ReachableSpanMortality, FiniteDimensionDetection, SubspaceEscape: bounded orbit spans and the dimension-of-subspace escape lemma. Only the short-orbit route is retained.
- ShortQuadraticObservation: symmetric coordinates, conjugation and affine lift. FiniteMortalityCompression: finite compressed-return group and positive-definite invariant form.
- RankSensitiveMortality, MortalityBudget, ImprovedMortalityBound, MinimumRankBound: surjective matrix defect, exact recurrence, mortality and positive minimum rank. Old uniform scalar-observation/descent routes are omitted.
- RankOneTrace, PlaneEllipse, RankOneSandwich, PlaneInvariantForm, TwoDimensionalMortality: trace quantization, three projective directions and shortening length five to four.
- MortalityExtremizer: the classical Černý C3 zero-sum-plane pair, with explicit finite closure and exact threshold; it is not claimed as a new lower construction.
- FlagMortality, LinearMortality, FlagQuotientMortality: invariant-subspace concatenation, basis transport, actual quotient actions, one/two-dimensional bounds. The concatenation method follows Almeida–Steinberg (2009), Lemma 2.4 and Proposition 2.5.
- BlockMortality, SharpFactorExamples: independent blocks and exact summed thresholds; local planar irreducibility.
- BoundedMortality: real-linear operators on the complex plane, contraction bounds, finite generator powers, mortality and exclusion of all words of a specified short length.
- MortalitySLP: valid acyclic relative references, word expansion, monoid evaluation, sandwich sharing and cubic gate bound. No synthesis-time/bit-complexity theorem.

Storage conventions: matrix words multiply in list order. Operators act on column vectors from right to left. SLP output is the first stored gate, with dependencies in its tail; references are relative indices. An empty-word gate counts toward size. The alphabet can be infinite; finiteness is required of the entire product monoid.
