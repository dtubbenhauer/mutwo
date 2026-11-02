# Review of the completed model comparisons

30 October 2026. This review concerns the additional comparison modules and
their use in `ModelComparisonCounterexample`. It supplements the original
manuscript audit; it does not replace a proof of the external literature
theorems. The reproducible validation result is in `reports/verification.json`.

## What the comparison actually identifies

The new polynomial lattice is a finitely generated `k[t]`-submodule of
`k[t,t^-1]^N` whose Laurent span is the ambient module. Its definition does
not refer to completed lattices, their degree, or the desired gallery count.
`PolynomialLattice.exists_basis_extending` verifies the basis condition in
Lusztig's definition. Completion takes the actual power-series span of the
natural image; algebraization takes its inverse image. Both inverse identities
are proved. No chosen truncation bound is part of either map.

The induced relative quotient equivalence is a map on vectors modulo actual
subspaces, including nonnested pairs. It proves preservation of the signed
degree defined separately in the two models. The same maps preserve lattice
order, intersections, sums, and the actual multiplication by `t^-1`.
Consequently `PolynomialFlags.flagEquiv` preserves all node orders, cyclic
containments, and absolute boundary degrees, for every retained mask.
`galleryEquiv` transports every intermediate flag and common refinement.
The argument establishes a bijection of galleries before comparing their
cardinalities.

There is an important distinction concerning changes of coordinates. An
arbitrary invertible Laurent-series matrix is not assumed to be a polynomial
matrix. `LatticeEquivariance` acts directly on completed lattices and proves
that its degree offset is independent of the lattice. One normalized endpoint
forces that offset to vanish. This transports a completed endpoint pair to
the explicitly completed polynomial pair, and then transports its entire
gallery. The separate orbit-quotient comparison uses the induced linear maps
on the actual intersection/sum quotients. Thus neither comparison relies on
an unproved approximation of an ambient invertible matrix.

The absolute coordinate normalization is also checked directly:
`coordinateQuotientEquiv` identifies the quotient of the first-`a` enlarged
coordinate lattice by the standard lattice with `k^a`, including `a=0` and
`a=N`. Hence its signed degree is `a`. For an affine window the degree offset
is additive under composition. Each Coxeter generator is an involution, so
its integer offset is zero; generation gives degree preservation for the
whole balanced affine group. This argument does not assert degree preservation
for the extended affine group's nonzero-degree translations.

The rational comparison also starts with independent objects. The coordinate
algebra is the image of matrix-entry polynomial evaluation on `SL_N(k)`.
Over an algebraically closed field, its kernel is proved to be exactly
`(det - 1)`. This is not merely an equality with the radical of that ideal:
the determinant-one equation is proved squarefree, using its column Euler
derivation, and the ideal is proved radical. The project then uses mathlib's
Nullstellensatz. All characteristics and the empty-matrix case are covered.
This identification with the determinant quotient is *not* asserted for
point functions over an arbitrary finite field. The final application uses
`PrimeClosure p`, which is algebraically closed.

The coproduct, counit and adjugate antipode give an actual mathlib Hopf algebra.
Tensor evaluation is proved injective. Independent coordinate comodules and
polynomial point actions are mutually reconstructed; intertwiners and the
tensor-image condition for invariant subspaces agree. This keeps the same
simple highest-weight module when changing models.

Finally, the tensor differential evaluates as
`d1 f(g,h) = g*f(h) - f(g*h) + f(g)`, while the degree-zero differential is
the actual coboundary. Their kernel/image quotient is linearly equivalent
to the existing `RationalH1`. The comparison preserves cocycles and
boundaries, not just dimensions. The Andersen and BNP inputs in the new
coordinate formulation are proved equivalent to the old function-formulated
inputs; they are not stronger substitutes for those statements.

## Where the final proof uses these results

`ModelComparisonCounterexample.row_sum` uses
`PolynomialWebLiterature.toWebLiterature`. This conversion derives the
completed convolution and coordinate-quotient interfaces from the polynomial
ones by the proved maps above.

`ModelComparisonCounterexample.named_row_and_lower_bound` and
`not_absoluteBoundedness` additionally use
`CoordinateLiteratureTransfer.Inputs.toFunctionInputs`. Their conclusions
are the original named PSL module and first-cohomology statements. The
ordinary lower index remains `w0`; the rank-dependent AJS threshold, the
separate BNP characteristic bound, and the actual restriction and central
quotient constructions have not been replaced by numerical stand-ins.

The uniform conclusion remains the row sum `choose(m+1,2)` and the resulting
unbounded maximum. This comparison does not establish the stronger individual
formula `mu_(j;m)=j`, a fixed-characteristic result, or new individual KL
certificates.

## What “modulo literature” still means

The remaining inputs are explicitly listed in `literature-inputs.md` and
printed in `AxiomAudit.lean`. In particular, these comparisons do not prove
the general Hecke/KL realization, the general polynomial Schur-convolution
theorem, or the representation-theoretic theorems.

One source-scope qualification is essential. The assumed normalized
polynomial convolution formula covers arbitrary finitary cyclic masks and
chains, with exponent `Chain.weight - length(w)`. It is a general consequence
assembled from the cited full-flag convolution framework and finite-parabolic
refinement, not a verbatim statement of Cui's Lemma 7.1. The complete-flag
lifting/fiber-count derivation is explained in `audit-primary-affine.md`;
it has not itself been formalized here. The completed/polynomial equivalence
does not supply that derivation. [Cui, §7](https://arxiv.org/html/1407.4557v3)
and [Williamson, §2.3](https://arxiv.org/pdf/1010.1283v3) support the geometric
identification and algebraic composition framework with the conventions
recorded in that audit.

Likewise, the identification of the regular bar complex with *derived*
rational cohomology remains the cited Jantzen theorem. The new kernel/image
comparison does not claim to formalize derived functors. The original-source
access limitation for Andersen is retained in `audit-andersen-followup.md`;
the existing precise formulation is also supported by the audited Lübeck
statement. No quantum or category-O theorem is substituted for the modular
theorem.

Thus the two working-model comparisons are proved constructions on the final
proof path. The final result remains conditional on the documented general
literature statements and their explicitly described consequences. A clean
foundational axiom audit does not, by itself, prove those hypotheses or verify
their citations. This is not an unconditional Lean counterexample.
