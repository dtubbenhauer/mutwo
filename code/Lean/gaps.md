# Gaps, qualifications and possible improvements

Updated 2 November 2026. No definite mathematical contradiction or missing
original lemma in the manuscript has been established by this audit.
Unformalized literature inputs and incomplete coding are not themselves
mathematical gaps. The precise current completion status is in `status.md`.

## Updated manuscript and seed coverage

The updated `main.tex` was compared with the development; see
[audit-updated-manuscript.md](audit-updated-manuscript.md). The main row sum
and eventual-prime counterexample are unchanged. The independent source
check of Andersen's original text remains outstanding; the checked
Lübeck formulation is the paper's stated route.

The previously documented §7 seed coverage gap is closed.
`SeedRankOne.canonical_identity` proves the correction from the actual
word's complete standard expansion. `SeedDecomposition.web_expansion`
proves both retained-line multiplicities one and the exact five-term
vector identity. `SeedPolynomials.diagonal_polynomial` then proves
`P_(w0,C_(2;2))=1+4X+5X²+4X³+2X⁴`, with the same fixed source and existing
literature inputs. The smaller polynomial is also proved. See
[audit-seed-coverage.md](audit-seed-coverage.md). No seed identity is a
literature premise; the uniform row-sum proof does not require the example.

The transfer interface proves the eventual-prime application. It does not
separately formalize the intermediate proposition at every prime where a
character formula is independently known; see
[audit-updated-transfer.md](audit-updated-transfer.md). Global web-category
equivalence and the new illustrative toroidal graph discussion also remain
outside the formalized claims. These are scope qualifications, not findings
that the paper's argument is false.

## Elementary assumption boundary: reduced

The earlier phrase “modulo the cited literature” included some elementary
consequences and assembled normalization. Those identified obligations are
now proved: see [audit-elementary-inputs.md](audit-elementary-inputs.md).
The matrix-length identity and full-to-partial convolution normalization
are internal proofs. The final bundle retains the genuine full-flag
orbit/Hecke realization, canonical Schur compatibility, and the other
major theorems listed in `literature-inputs.md`. The separate Schur-support
input is now derived from refinement. Bar involutivity and family-action
nontriviality are also proved; the unused Andersen finiteness clause is
removed. See [audit-input-necessity.md](audit-input-necessity.md). This corrects the earlier
formalization boundary; it is not a newly discovered contradiction in the
manuscript.

## Withdrawn integral-presentation concern

An earlier review questioned whether an integral annular-presentation
comparison was needed. Rechecking the manuscript resolved this: it already
defines the six integral parabolic module maps. Their composite and cleared
numerator identity are now formalized directly. Thus a general equivalence
of annular web presentations is not needed for this coefficient argument.
One should still distinguish integral SSW results from the generic thin-dot
presentation over `C(q)`.

## Framework comparisons and cited normalization

The polynomial/completed model comparison is now proved globally, including
degree, shifts, arbitrary flag masks, galleries and orbit-coordinate
quotients. The final route starts with `PolynomialWebLiterature` and derives
the original completed interface. See `audit-model-comparisons.md`.

The full-to-partial fiber count and normalization are now kernel-checked;
see [audit-full-flag-normalization.md](audit-full-flag-normalization.md).
The remaining external statement is full-flag orbit classification and
binary affine Hecke convolution in the polynomial model. It is a precise
source-level formulation of Lusztig/Cui, not a claim that the project's
record is a verbatim numbered lemma. Williamson §2.3 directly covers
arbitrary finitary canonical corners and refinement. Formalizing those
major theorems themselves would go beyond the requested literature boundary.

## Fixed-source transfer and characteristic bounds

The cohomological application requires the ordinary source `w0`, the
inverse-dot label, the eventual AJS rank-dependent threshold, restrictedness,
and the separate BNP bound `p>=5(N-1)`. These conditions are explicit in the
formal transfer and checked for the family. Unbounded coefficients with an
arbitrary lower endpoint would not suffice.

The original BNP theorem guarantees a cohomology isomorphism in the stated
specialization. The Lean input assumes an isomorphism, not an unverified
claim about which particular restriction map realizes it. Further work
could formalize that theorem and Andersen/AJS themselves. No stronger
small-characteristic statement is being claimed.

The primary-source follow-up recovered AJS and confirmed the stated
restricted-region threshold, and checked Jantzen, BNP and Steinberg. The
original Andersen formula has not yet been inspected; its precise
fixed-source convention is still supported through Lübeck. The formerly
unproved regular-function comparison is now closed in Lean: the exact
determinant coordinate ring, faithful tensor evaluation, representation and
submodule correspondence, and regular-cochain quotient equivalence are
constructed. See
[audit-rational-coordinate-comparison.md](audit-rational-coordinate-comparison.md).
The derived-cohomology comparison itself remains the cited Jantzen theorem.

## Scope of the conclusion

The target is the paper's row sum, giving an unbounded maximum. It does not
prove the conjectural individual formula `mu_(j;m)=j`. The two seed
polynomials are now separately proved by the paper's web calculation.
Those examples are not needed for the uniform row-sum route.

An unconditional Lean disproof requires formal proofs of the entire
literature ledger. Completion modulo those explicit literature inputs is
logically different and is labeled as such in the final theorem and README.

## Specific graphical identification: closed

The earlier audit correctly noted that matching boundary masks alone did
not identify `Web.family` with the six-map element. That missing bridge is
now proved for the paper's fixed cut-open presentation:
`WebTraceEvaluation.family_graph_evaluation_eq_raw`. The stronger theorem
`WebProof.graph_morphism_eq_sixMaps` identifies the full right Hecke-module
map, and `graph_corrected_critical` gives the critical readout on the
corrected actual graph evaluation.

The proof checks all fourteen local operations, exact ordered ports and
frontiers, the entire graph and its separate winding edges, every absolute
boundary mask, and the split/merge composition laws. Canonical recuts
preserve each named packet's absolute thin positions and satisfy a proved
winding invariant. Full turns are rejected, not interpreted as identities.
No additional literature assumption was added to close this gap.

See [graph-evaluation.md](graph-evaluation.md) and the independent review
[audit-graph-winding.md](audit-graph-winding.md), together with the
implementation review [audit-graph-evaluation.md](audit-graph-evaluation.md).

The result evaluates a **checked presentation** of the concrete graph. It
does not establish independence under arbitrary alternative presentations
or annular isotopies, or construct the entire SSW category and its rotation,
braid and dot calculus. Those broader questions remain outside this
formalization; they are not being used to fill the specific original gap.


## Three generic assumptions discharged

Nonvanishing and bar invariance of the actual parabolic scalar, and the
actual one-period lattice lift, are now proved in Lean. The corresponding
three input fields have been removed, without adding replacement
assumptions. See [audit-assumption-reduction.md](audit-assumption-reduction.md).
This improves the formalization but does not remove the external geometric
and representation-theoretic source theorems described above.


## Further lattice progress and completed assembly

The whole `LaurentLattice.Theory` input is now constructed in Lean: period
finiteness/dimension, relative-quotient finiteness and the signed-degree
formula. It is no longer a field of the external literature bundle. The
natural finite-truncation comparison and actual bounded-lattice
correspondence are also proved; see
[audit-lattice-completion.md](audit-lattice-completion.md).

The full polynomial/completed-lattice equivalence and its flag, degree,
gallery and coordinate compatibility are now assembled; see
`audit-model-comparisons.md`. Finite flag enumeration, partial-gallery normalization and the matrix
dimension identity are now also internal proofs. The remaining source-level
full-flag theorem is identified above.

The [Andersen follow-up](audit-andersen-followup.md) identifies §2,
Propositions 2.8 and 2.12 of the original paper as the precise source targets.
The original text remains inaccessible. Accessible quantum/category O
analogues are not substituted for the required modular fixed-source theorem.
