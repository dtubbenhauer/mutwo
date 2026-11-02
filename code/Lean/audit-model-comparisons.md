# The completed model comparisons

**Subsequent status:** the remaining elementary obligations described in
this review have now been discharged, including parabolic laws, matrix
lengths and full-to-partial convolution normalization. The final web bundle
has only `refinement` and `full_flag` fields: Schur support is derived from
refinement. See [audit-input-necessity.md](audit-input-necessity.md),
[audit-elementary-inputs.md](audit-elementary-inputs.md) and the current
`literature-inputs.md`; the review below records its earlier scope.

The final comparison endpoint is
`ModelComparisonCounterexample.not_absoluteBoundedness`. Its geometric
inputs use polynomial Laurent lattices; its cohomological inputs use the
coordinate-ring tensor complex. The conversions into the manuscript's
working models are proved, rather than fields of those input bundles.

## Polynomial lattices and completed flags

`PolynomialLattice.Lattice` consists of actual finitely generated
`k[t]`-submodules of `k[t,t⁻¹]^N` which span the Laurent ambient module.
`PolynomialLattice.exists_basis_extending` proves that each admits a
`k[t]`-basis which is also a Laurent-polynomial basis, matching Lusztig's
definition literally.

Completion is the `k[[t]]`-span of the natural image. Algebraization is
inverse image under the coefficientwise inclusion. `LatticeCompletion.orderIso`
proves these are inverse order isomorphisms for all lattices. The maps do
not depend on chosen truncation bounds; finite approximations are used only
in their proofs.

The comparison preserves:

- Actual relative quotient spaces, via `LatticeCompletion.quotientEquiv`.
- The independently defined signed degree and multiplication by `t⁻¹`.
- The literal coordinate monomials and affine-window coordinate lattices.
- Flags with arbitrary retained masks, their restrictions, common
  refinements, galleries and cardinalities (`PolynomialFlags`).
- Intersections, sums, block quotients and cumulative quotients used in
  the periodic matrix coordinates (`PolynomialOrbitCoordinates`).

`LatticeEquivariance` proves the effect of an arbitrary Laurent-series
linear change of basis. It preserves relative quotient dimensions; once
one anchor has the prescribed degree, it preserves all absolute degrees.
Its flag and gallery equivalences reduce arbitrary completed endpoint pairs
to the literal polynomial coordinate pairs. No polynomial approximation of
an arbitrary invertible Laurent-series matrix is assumed.

`PolynomialFlagConvolution.Input.toCompleted` and
`PolynomialOrbitCoordinates.Input.toCompleted` then supply the old
completed-model interfaces. `PolynomialWebLiterature.toWebLiterature`
assembles them. Gallery finiteness is proved separately from lattice
incidence and is no longer an assumed convolution field. The canonical
endpoint flags are also constructed: the coordinate quotient has an actual
basis of size `a`, hence degree `a`; balanced window actions preserve that
degree. `PolynomialCoordinateFlags` proves that their node modules are
exactly the ordinary coordinate lattices and the literal polynomial-window
translates. Thus endpoint realization is not a literature assumption.

## Rational modules and first cohomology

The independent coordinate-algebra comparison is detailed in
[audit-rational-coordinate-comparison.md](audit-rational-coordinate-comparison.md).
It proves the exact determinant-one quotient over an algebraically closed
field, faithful tensor evaluation, the Hopf operations, the
action/comodule round trips, agreement of invariant subspaces, and the
regular tensor-cocycle quotient equivalence.

`CoordinateLiteratureTransfer` states Andersen/AJS and BNP using this
tensor-cohomology space. Its input-equivalence theorems show that the
conversion preserves all indices and hypotheses. The final endpoint
combines this proved conversion with the polynomial flag conversion.

## What remains cited input

The new proofs do not prove the general affine Hecke/Schur realization,
ordinary KL positivity, polynomial orbit/matrix enumeration, finite flag
enumeration, or the representation-theoretic theorems. Their statements
remain explicit arguments, as recorded in `literature-inputs.md`.

In particular, normalized polynomial Schur convolution for arbitrary
finitary masks is a general framework statement derived from the cited
Lusztig/Cui realization and finite-parabolic refinement normalization. It
is not presented as the verbatim text of Cui Lemma 7.1. The mathematical
source derivation through complete-flag lifts and their Poincaré factors
is recorded in `audit-primary-affine.md`; that full derivation is not itself
claimed as kernel-formalized here. The proved completion comparison does
not substitute for the external convolution theorem.

Likewise Jantzen's theorem that the regular bar complex computes derived
rational cohomology, and Andersen/AJS, BNP, Steinberg and PSL simplicity,
remain the previously documented literature inputs. The result is a
machine-checked conditional counterexample, not an unconditional Lean
disproof.

## Final verification

`python3 scripts/verify.py` passed: **174 Lean sources built and 213
principal declarations audited**. All reported axioms are among `propext`,
`Classical.choice` and `Quot.sound`. Certificate regeneration is identical,
and the manuscript hash is unchanged. The final import closure contains
both comparison branches and the named-family endpoint. The exact theorem
and input types are printed in `reports/axioms.txt`; the machine-readable
result is `reports/verification.json`.

The independent review in `audit-model-comparison-review.md` and a second
cross-check of the polynomial conversions found no missing model bridge.
Those reviews retain the normalized-convolution source-scope qualification
above; the full build does not prove the external literature hypotheses.
