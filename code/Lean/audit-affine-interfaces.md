# Review of the affine matrix and flag interfaces

Review date: 30 October 2026. This is a review of the current Lean interfaces,
not a proof that the external inputs have been constructed in Lean.

## What the original calculations establish

The family is an actual balanced affine permutation, obtained by sorting the
prescribed shifted window. Its period-three matrix, all columns outside the
three supported columns, its inversion-length gap and its required left and
right descents are proved uniformly. The ordinary lower endpoint remains the
finite longest element throughout.

`SixFlagGallery`, `SixFlagData` and `QuotientFlagData` prove the equivalences
from the particular six boundary masks to actual lattice incidences and then
to finite-vector-space galleries. `GalleryCounting` counts those actual
configurations using general Gaussian subspace formulas. No special gallery
count is a field of the general convolution input.

`PacketIndexClassification` uses general matrix injectivity only after the
family's actual matrix and maximality are proved. Type F identifies the
original upper endpoint. The full type identifies the actual spherical
index even when only fine-corner maximality is initially known.

`PacketCoarsening` checks a useful original mechanism: merging adjacent rows
adds the crossing term `sum (c<h) A_top,c A_bottom,h` to the periodic dimension.
That term vanishes for the strong and weak one-line types. General
maximal-length uniqueness then proves coarse maximality of the same index.

## General inputs and their scope

- `LaurentLattice.Theory`: finite quotient dimensions, relative degree,
  period dimension, and the lifting of every subspace in a one-period
  interval to a full lattice. The ambient objects are actual finitely
  generated `k[[t]]`-modules spanning `k((t))^N`.
- `OrbitMatrix.CoordinateDimensionInput`: the general intersection-quotient
  and cumulative coordinate counts, plus coordinate containment criteria.
- `OrbitMatrix.ThreeColumnLengthInput`: general periodic matrix dimension,
  maximal-representative injectivity, and its maximal-length converse.
- `FlagConvolution.Input`: existence of endpoint realizations, finiteness
  of arbitrary chain galleries, and the normalized convolution coefficient
  for arbitrary chains. It has no original-family polynomial or support input.

[Cui, §7.1 and Lemma 7.2](https://arxiv.org/html/1407.4557v3) give the
periodic dimension with row inequality `i >= k`, and identify it with the
maximal double-coset length minus the source-longest length. The converse
criterion also uses uniqueness of the longest element of a finite-parabolic
double coset; it is a consequence of that general framework, not a separate
family theorem. Cui's Lemma 7.1 identifies orbit convolution with the Schur
algebra. [Du–Fu, §2](https://arxiv.org/pdf/1311.1868) gives the block-count
matrix indexing and normalized standard basis.

There is a scope qualification: Cui's displayed lattice model uses
polynomial Laurent modules, while this project uses completed Laurent
series. The general equivalence of the bounded finite-quotient flag problems
under completion is included in the unformalized framework input. A citation
to Cui alone is not a Lean proof of that equivalence. This does not import
the manuscript's six-mask bijection or four-case count.

## Normalization checks

The Hecke relation is `(H_s-v^-1)(H_s+v)=0`, with trivial finite eigenvalue
`v^-1`. The convolution input specializes at `v=1/p` over a field of order
`p^2`; thus the counting parameter is exactly `Q=v^-2`. Its exponent is the
sum of actual parabolic length increments minus the actual endpoint length.

Two independent structural checks agree with this convention. A nil chain
at a finite-parabolic element has coefficient `v^(ell(w_I)-ell(w))` and one
compatible endpoint configuration. A split from a full boundary followed
by its merge gives the parabolic Poincaré quotient, with the same power of
`v` as the flag-count normalization. The interpolation theorem proving an
identity from all prime-square specializations is internal Lean mathematics.

The canonical dictionary uses ordinary affine KL polynomials with source
`w0`, not source `1`; the inverse spherical label is `w0*u^-1`. These labels
are proved equal to the corresponding inverse upper endpoint before the
cohomological transfer is applied.

## Limits of this review

No false external interface was identified in these checks. This is not an
independent formal construction of the cited Coxeter, KL, completed-lattice
convolution or representation-theoretic theorems. Final claims must still
list their explicit literature hypotheses and any original assembly lemmas
not yet discharged; a successful conditional build alone cannot establish
an unconditional counterexample.
