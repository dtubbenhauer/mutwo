# Formalization status

Updated 2 November 2026 after comparison with the revised manuscript and
`Lean_verification_recommendations.pdf`. The source hashes are in
`certificates/manuscript-review.json`. This replaces the earlier audit status.
The intended target is the row-sum counterexample of `../main.tex`, not the
stronger conjectural individual rule `mu_(j;m)=j`.

## Final validation

The build covers 249 project Lean sources. There are 293 principal axiom
checks, each protected by a failing `#guard_msgs`, plus 17 guarded
interface/conclusion definitions and five explicitly typed endpoint
applications. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed (some theorems use none). The reproducible full check is
`python3 scripts/verify.py`; its latest outcome is in
`reports/verification.json`. Both
model-comparison branches occur in the final theorem's checked import
closure (`reports/fidelity-import-closure.json`).

The reproducible verification report is `reports/verification.json`, with
full build output in `reports/lake-build.txt` and the separate axiom/type
audit in `reports/axioms.txt`. The final theorem
`ModelComparisonCounterexample.not_absoluteBoundedness` is checked **from the explicit general literature inputs**. No original
web count, canonicality, correction, row sum or family transfer equality
remains as an extra premise of that theorem.

The mathematical library and audit have separate targets, both built by
default. Negative controls must reject an incorrect axiom expectation and
an extra unavailable theorem premise. The verifier checks pinned dependency
revisions and tracked-source cleanliness, certificate regeneration, the
reviewed manuscript hash, and unchanged sources throughout the run. Its
content-addressed source manifest is local release evidence, not a published
repository revision or a claim that hosted CI is configured.

## Comparison with the revised paper

The explicit family and core proof still agree with `main.tex`; the main
target remains the row sum. No stronger individual formula has been added
to the formalization. See [audit-updated-manuscript.md](audit-updated-manuscript.md)
for the comparison and decisions on all five recommendations.

The field-level [framework ledger](audit-framework-inputs.md) and
[transfer ledger](audit-updated-transfer.md) give exact statements, sources
and convention conversions. Original Andersen full-text verification
remains outstanding; the paper's Lübeck formulation is the checked route.
The final eventual-prime theorem matches the paper, while its intermediate
transfer at any prime where the character formula holds has not been
separately formalized with a character-formula predicate.

The §7 seed coverage gap is now closed. `SeedRankOne.canonical_identity`
proves the rank-one correction from the full actual standard expansion;
`SeedDecomposition.web_expansion` proves the exact five-term canonical
decomposition, including both retained-line multiplicities one.
`SeedPolynomials` proves the four-web vector identity and both actual
ordinary fixed-source KL polynomials. See
[audit-seed-coverage.md](audit-seed-coverage.md). No seed equality or new
literature input is assumed. Canonical refinement remains cited input, as
in the paper. Global annular category equivalence, arbitrary isotopy and
the illustrative toroidal closure are not claimed.

## Elementary-input reduction

The earlier assumption boundary was too broad for the requested
“major theorems only” standard. The identified elementary obligations are
now proved and used by the final theorem. They include finite flag counts,
actual coordinate formulas, inversion and diagram invariance, proper
parabolic longest elements and lengths, finite symmetrizer identities,
coset factorization, integral inclusions and merges, the matrix dimension
identity, and the full-to-partial convolution normalization.

The final `PolynomialWebLiterature` structure has exactly two fields:
`refinement` and `full_flag`. The latter contains full-flag orbit
classification and binary affine Hecke convolution. It contains no
partial-gallery count, Poincare factor or arbitrary-chain formula. The
removed assumptions are tracked in [audit-elementary-inputs.md](audit-elementary-inputs.md).
The explicit configuration bijection and normalization are explained in
[audit-full-flag-normalization.md](audit-full-flag-normalization.md).

## Necessity audit

The former Schur-product support input is derived from refinement by actual
standard-sum eigenconditions and finite canonical-support induction. Bar
involutivity is derived from the bar-fixed canonical basis. The family action
is proved nontrivial by a concrete prime-field torus element, so the Steinberg
input now supplies only irreducibility. The unused finite-dimensionality
clause was removed from both Andersen interfaces; their dimension equality
and the BNP isomorphism suffice for the same final theorem.

The remaining inputs have distinct roles: five framework packages enter the
web row sum; five representation packages are added for the faithful finite
PSL application. This is a dependency inventory, not a claim of logical
independence. See [audit-input-necessity.md](audit-input-necessity.md) for actual
consumers, stronger-than-needed scopes, and which references are background.

## Fully proved components

These are kernel-checked mathematical arguments, with ordinary mathematical
parameters as displayed in their types and no new axioms:

- Actual affine permutations, periodic action, sorted family windows,
  matrix entries, inversion-count formulas and inverse-dot weights.
- The graph and ordered/ribbon/boundary/winding data for the main web;
  exact checked replay of all fourteen operations, ordered and winding-sensitive
  frontiers, all fifteen local boundaries, and actual absolute thin positions.
  Restricted recuts satisfy a winding invariant and reject full turns.
- Evaluation of the concrete checked graph presentation; equality of its
  complete right Hecke-module morphism with the manuscript's six maps, and
  equality of all standard/canonical coordinates. The corrected actual
  graph has critical coefficient `choose(m+1,2)` at the fixed source.
- Uniqueness of the KL interface's standard basis, bar, canonical basis
  and polynomials on a fixed Coxeter model; exact agreement of the weight
  vector and Dynkin labels with the manuscript's fundamental-weight formula.
- Actual integral inclusion/merge composites and their cleared identity,
  given general parabolic laws. Bar and numerator positivity follow from
  the corresponding general ordinary Hecke inputs.
- The full one-period lattice lift, constructed from power-series stability,
  an injective multiplication-by-t map, and Noetherianity; both interval
  endpoints are checked. Parabolic scalar nonvanishing and bar invariance
  are derived from the actual sum and existing absorption law. These three
  properties have been removed from the assumed structures.
- The complete general lattice-theory bundle: an actual period equivalence
  with k^N, finite relative quotients by denominator clearing, actual
  standard/intersection lattices, and the exact signed-degree formula.
  `provedTheory` supplies these facts; they are no longer an external field.
- The natural polynomial/power-series quotient equivalence modulo t^d,
  preservation of stable-subspace incidence and the stated dimensions, and
  the exact correspondence for actual bounded lattice intervals. The global
  completion/algebraization order equivalence is now also proved, preserving
  relative quotients, signed degree, shifts, flags, refinements and galleries.
- The polynomial basis condition in Lusztig's definition; literal monomial
  window endpoints with directly proved absolute degrees and canonical
  endpoint flag realization; polynomial/completed block and cumulative quotient
  equivalences; arbitrary Laurent-coordinate flag/gallery equivariance.
  These supply the completed convolution and coordinate interfaces from
  the polynomial-model literature inputs.
- The exact determinant-one coordinate ring over algebraically closed
  fields, its Hopf algebra, faithful tensor evaluation, polynomial-action
  and comodule round trips, intertwiners and invariant subspaces. The tensor
  regular complex and its H¹ kernel/image quotient are proved equivalent
  to the original polynomial-function cohomology model.
- Actual six-map lattice-gallery and quotient-gallery bijections; the
  four-case finite count; support and cumulative rank calculations.
- Generic polynomial identities used in Gaussian cancellation, exact
  correction, degree bounds and critical coefficient extraction, proved
  uniformly rather than by finite-range extrapolation.
- Actual auxiliary gallery bijections and canonicality from their computed
  standard coefficients; full-spherical transitions and affine reflection.
- Concrete family index identification, matrix coarsening, multiplicity
  bounds and the contribution margins required by the readout.
- Highest-weight family coordinates, all dominance/restrictedness/regularity
  conditions, root-lattice central action, central-quotient H^1 equivalence,
  finite-dimensionality of finite-group H^1, and absolute irreducibility
  over an algebraic closure.

“Given general inputs” is not the same as an unconditional theorem. The
next section identifies the remaining major theorem inputs and source qualifications.

## Conditional on the general cited literature

`Hecke.TheoryFamily`, `PolynomialWebLiterature`, and
`CoordinateLiteratureTransfer.Inputs` remain
explicit hypotheses. They include the affine Coxeter/KL framework, ordinary
positivity, canonical refinement span, full-flag orbit
classification and binary Hecke convolution, highest-weight existence, Andersen/AJS,
BNP, Steinberg restriction and PSL simplicity. Their precise statements,
sources, normalizations and source-checking limitations are in
`literature-inputs.md`. Full-lattice theory and both model comparisons are
proved constructions, as are finite flag enumeration and polynomial orbit
coordinates. The normalized partial-gallery formula is now derived from
the full-flag theorem: actual full lifts exist, their cardinalities are
proved, an actual configuration bijection supplies the fiber product, and
the integral cleared identity supplies the exponent and cancellation.
The matrix dimension/length formula is also internal finite combinatorics.
The new primary-source audits are `audit-primary-affine.md` and
`audit-primary-transfer.md`: original AJS, Jantzen, BNP and Steinberg were
checked, while Andersen's original full-text convention check remains a
source-access qualification. The explicit model comparisons are now proved;
see `audit-model-comparisons.md`, `audit-rational-coordinate-comparison.md`,
and the independent `audit-model-comparison-review.md`. See
`audit-assumption-reduction.md` for the earlier three reductions and
`audit-lattice-completion.md` for the complete proved lattice bundle and
finite comparison. `audit-andersen-followup.md` records the more precise
original-source targets; the modular theorem is not replaced by its
quantum/category O analogues.

The final declarations are:

| Declaration | Conclusion |
|---|---|
| `WebProof.row_sum` | Actual fixed-`w0` ordinary KL row equals `choose(m+1,2)` |
| `WebProof.row_two`, `row_three` | Row totals 3 and 6, as consequences of the uniform theorem |
| `LiteratureTransfer.familyModule_h1_dimension` | The actual named PSL module has the actual KL coefficient as H^1 dimension |
| `WebProof.named_row_and_lower_bound` | At every sufficiently large prime, the named faithful absolutely irreducible modules have the required row sum and maximum at least `floor(m/2)+1` |
| `WebProof.not_absoluteBoundedness` | No universal H^1 bound over all fields, finite groups and faithful finite-dimensional absolutely irreducible modules |
| `ModelComparisonCounterexample.named_row_and_lower_bound` | Same named family and bounds, passing through both proved model conversions |
| `ModelComparisonCounterexample.not_absoluteBoundedness` | The final counterexample with polynomial-lattice and coordinate-cohomology literature inputs |

No original count, canonicality, correction or row theorem is an extra
hypothesis of `WebProof`. Its remaining dependencies are exactly the general
literature/framework inputs described above.

## Finite certificates and experimental checks

The fourteen window/matrix/weight certificates for `2<=m<=5` and an invalid
certificate rejection are kernel checked. They certify actual affine data;
they do not certify the AJS threshold or compute ordinary KL polynomials.

The actual individual seed KL polynomials are now proved in
`SeedPolynomials.lean`, following the manuscript's canonical web argument.
The finite affine-window checks support actual coset and retained-line
identifications; their arithmetic is kernel checked. The Python KL and
finite arithmetic checks remain explicitly untrusted comparisons, not
formal proof steps. The fresh audit
also passes direct finite-set counts for all 20 small gallery matrices,
30,660 periodic window/composition checks and 8,214 finite-flag formulas;
these are experimental only. See `audit-fidelity.md` and its linked reports. The uniform row
calculation does not depend on their outputs.

## Not formalized or not claimed

- Proofs of the remaining general external inputs; the lattice-theory
  component is now proved, but no unconditional
  Lean counterexample has been obtained.
- Independence of evaluation under arbitrary graph presentations or
  annular isotopy; a global SSW quotient/evaluation equivalence. The specific
  fixed graph-to-six-map identification is proved; see `graph-evaluation.md`.
- The individual formula `mu_(j;m)=j`, a fixed-characteristic unboundedness
  theorem, or certified individual KL rows for `m>=3`. The two `m=2`
  polynomials are now proved.

No definite mathematical gap in the manuscript has been established.
`gaps.md` records the resolved integral-presentation and specific
graph-evaluation concerns, together with the remaining framework qualifications. All manuscript and pre-existing research files
remain unchanged.
