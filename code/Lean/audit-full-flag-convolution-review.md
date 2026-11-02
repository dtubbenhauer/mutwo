# Review of the full-flag convolution reduction

This review concerns `FullFlagHeckeConvolution.lean`,
`FullFlagHeckeCounting.lean`, and their connection to the full-lift and
normalization modules. It is a source and semantic review, not a proof of
the cited affine Bruhat/convolution theorem.

## The external boundary

`FullFlagHeckeConvolution.Input K p hp` has exactly two fields:

1. `orbits`: each pair of actual full polynomial flags has a unique actual
   balanced affine permutation as relative position;
2. `convolution`: the Hecke kernel of a binary product is convolution of
   the two kernels over actual full middle flags.

The kernel is **defined**, not freely chosen: at a pair of relative
position `w`, it is `v^length(w)` times the specialized normalized standard
coefficient. Relative position itself is defined by a single invertible
Laurent-polynomial-linear map taking coordinate modules to the target
nodes and the corresponding window-transformed coordinate modules to the
source nodes. Thus the orbit field cannot be satisfied by assigning
arbitrary numerical labels to abstract states.

The input contains no partial masks, longest elements, symmetrizers,
Poincare polynomials, partial galleries, family parameters, prescribed
coefficient, or multi-step formula. In particular, the previous general
normalized partial-gallery formula is not a field of this input.

## Sources and the precise translation

The source text checked is the retained author copy of Lusztig,
*Aperiodicity in quantum affine gl_n*, §§1.3–1.9, and
`../../RevisedWeb/references/cui.txt`, §7.1.

- Lusztig §1.3 uses free modules over `k[epsilon,epsilon^-1]` and polynomial
  lattices. Lemmas 1.4–1.5 give simultaneous decompositions and the orbit
  classification by periodic intersection matrices.
- Lusztig §1.7 defines finite two-orbit convolution fibers; §§1.8–1.9 give
  their structure constants and the characteristic-function convolution
  algebra. The multiplication displayed at the end of §1.10 has target,
  middle, source in the same order as the Lean kernel.
- Cui §7.1 explicitly includes complete periodic lattices, with every
  successive quotient of dimension one. Its Lemma 7.1 identifies the
  orbit convolution algebra with the affine Hecke/Schur realization.
  In the full-flag corner this is the affine Hecke algebra.

The exact Lean record is the **full-flag, fixed-degree version** of these
framework theorems, expressed in the project's conventions; it is not a
verbatim statement numbered “Lemma 7.1” in Cui. Periodic permutation
matrices index full-flag orbits. Fixing the absolute degree of node `i` to
`i` restricts the extended affine indexing to balanced windows. The
existence and uniqueness part of that full-flag orbit theorem is external;
Lean does not construct an inhabitant of `Input` from the printed papers.
The existing polynomial-lattice, coordinate, degree and completion
comparison modules supply the project's underlying model, not another
assumed comparison map.

The source parameter usually denoted `v` specializes to `sqrt(Q)`;
Lean's parameter is its inverse. With `Q=p^2`, the code uses `v=1/p` and
`H_w=v^length(w) T_w`. Consequently the kernel value is
`v^length(w) [H_w]x`. This conversion is built into the definition of
`value`; the parabolic and final chain exponents are then derived in Lean.
No ordinary-to-antispherical conversion occurs in this reduction.

## Checked elementary deductions

- `forget_eq_iff` proves that two full flags agree on `retained I` exactly
  when their relative window belongs to the actual generated finite
  subgroup `W_I`. It cancels the injective common polynomial module map
  and applies the proved integer-cut stabilizer calculation. This works
  for every proper cyclic mask, including masks containing the affine
  node. No polynomial-to-completed action is assumed in this argument.
- `symmetrizer_coordinate` uses the proved finite canonical symmetrizer
  expansion. `value_symmetrizer` proves that its kernel is
  `v^length(w_I)` times the retained-cut agreement indicator.
- `symmetrizer_square_count` uses binary convolution and the proved
  absorption identity to give
  `specialize(h_I) v^length(w_I) =
   v^(2 length(w_I)) card(Lift(forget I F))`.
  The subsequent full-lift cardinality module cancels a proved nonzero
  unit and uses the proved scalar specialization. Full-refinement
  existence is a separate constructive finite-dimensional flag argument.
- `lastLiftEquiv` identifies the last middle flag with an actual full
  lift of the target partial flag. `fullGalleryFiniteByLifts` proves
  finiteness by induction, independently of convolution.
- `value_numerator_count` proves the arbitrary product formula by
  induction from **binary** convolution. `numerator_coordinate_count`
  proves the exact exponent `vertexWeight - length(w)` by cancelling the
  nonzero normalization factor.
- The separate configuration equivalence records one full lift of each
  actual common refinement. Its cardinality statement, combined with
  the Poincare lift count and the proved cleared numerator identity,
  supplies the partial-gallery normalization. The construction now builds
  as `PolynomialConvolutionConstruction.fromFullFlag` and replaces the
  old assembled convolution field in the final literature record. The
  complete project verification is recorded in `reports/verification.json`.

## Finiteness and trust

`Nat.card` and `finsum` have default values for infinite objects, so using
those expressions alone would be insufficient. Every convolution sum
used here is reduced by `finsum_indicator` to a finite subtype of actual
full lifts. Finiteness of these lift types was proved earlier by bounded
lattice quotients. Full-gallery finiteness is proved independently in
`fullGalleryFiniteByLifts`; partial-gallery finiteness is already proved
in `PolynomialFlags`. Thus no infinite default value is used as a count.
The external binary statement uses `finsum`, but its applications in the
reduction have explicitly finite support.

The new theorems use kernel-checked proofs. Their axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. There is no
`native_decide`, new axiom, numerical oracle, or assumption equating a
matrix with a cohomology operation.

## Conclusion and limits

The former partial-chain normalization is reduced to the genuine
full-flag affine orbit/Hecke realization plus explicit elementary
arguments. The new interface is faithful to polynomial lattices and the
actual balanced affine group; the source/target order, finite sums, and
normalization have been tracked.

This does not make the affine Bruhat/convolution theorem a Lean theorem,
and it does not independently prove any representation-theoretic
KL-to-H¹ transfer. Those remain explicit cited inputs elsewhere. A final
“modulo literature” claim also requires the final integrated build and
faithfulness audit of those other inputs; success of these two new modules
alone is not an unconditional counterexample.
