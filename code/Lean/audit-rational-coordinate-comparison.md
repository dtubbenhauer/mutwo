# The rational representation and cohomology comparison

This closes the polynomial-function/model comparison identified in
`audit-primary-transfer.md`. All changes are under `code/`; the manuscript
is unchanged. The remaining use of Jantzen is his cited theorem that the
regular bar complex computes **derived** rational cohomology, not an
assumption identifying two arbitrarily chosen function spaces.

The representation-theoretic application uses
`k = AlgebraicClosure (ZMod p)`. The algebraically closed hypothesis is
essential for the coordinate-ring comparison with evaluation on `k`-points.
The function and tensor constructions can also be written over other fields;
that does not identify finite-field point representations with rational
algebraic-group representations.

## The coordinate algebra

`SLCoordinateAlgebra.lean` constructs the algebra of polynomial functions
on the actual determinant-one matrices and proves its equivalence with
the polynomial ring modulo their vanishing ideal. The determinant and
Hopf-algebra companion modules establish the defining determinant equation
and the matrix multiplication, identity, and inverse operations. Thus the
coordinate algebra is attached to the actual special-linear variety; it
is not a vector space supplied by a cohomology-dimension hypothesis.

The generic `SLCoordinate.tensorEvaluation_injective` proves that evaluation
on ordered pairs distinguishes every element of a tensor product of
coordinate function spaces. `CoordinateTensor.lean` proves the vector-valued
version and reconstructs a coordinate tensor from its scalar coordinates
in a finite basis. Both directions are checked; agreement only on pure
tensors is not substituted for injectivity on their sums.

## Actual representations and invariant subspaces

`RationalCoordinateRepresentations.lean` defines
`CoordinateRepresentation` independently by a linear coaction
`V → V ⊗ k[SL]`, its counit identity, and its tensor coassociativity identity.
The coproduct is the one constructed from matrix multiplication.

The following declarations prove the comparison:

- `CoordinateRepresentation.pointAction` constructs a genuine group
  representation from a coaction; `pointRep_polynomial` proves polynomiality.
- `toCoordinateRepresentation` constructs a coaction from the existing
  polynomial action. `toCoordinateRepresentation_pointAction` and
  `coordinateRepresentation_roundtrip` prove the two round trips.
- `intertwiner_iff` identifies linear intertwiners of the point actions
  with the tensor coaction-intertwining equation.
- `invariant_subspace_iff` identifies pointwise invariance with the exact
  tensor-image subcomodule condition. Its proof uses tensor right exactness
  and evaluation injectivity after quotienting by the subspace.

In particular the comparison preserves irreducibility and the underlying
actual action. The torus eigenvector and upper-unipotent conditions in
`HighestWeight.lean` refer to that same action and those same matrices.

## Actual cochains and first cohomology

`RationalCoordinateCochains.lean` uses `C¹ = A ⊗ k[SL]` and
`C² = A ⊗ (k[SL] ⊗ k[SL])`. It constructs the tensor maps

```
d⁰(a) = δ(a) - a ⊗ 1,
d¹ = (δ ⊗ id) - (id ⊗ Δ) + (id ⊗ insertion of 1),
```

with the indicated associator. Evaluation gives exactly
`d⁰(a)(g)=ga-a` and `d¹(f)(g,h)=g f(h)-f(gh)+f(g)`.
Faithful evaluation proves `d¹ d⁰=0` in the actual tensor space.

`RationalCoordinateH1.lean` then defines the kernel of this `d¹` and the
image of the constructed `d⁰`. Its `CoordinateH1` is their quotient.
`cocycleEquiv` maps a tensor cocycle to its evaluated regular function;
`cocycleEquiv_boundaries` proves equality of the corresponding boundary
subspaces. Consequently

```
h1Equiv hA : CoordinateH1 hA ≃ₗ[k] RationalCohomology.RationalH1 A
```

is a proved quotient equivalence. It is not a supplied literature premise,
nor a definition that replaces one cohomology dimension by another.

`CoordinateLiteratureTransfer.lean` states the Andersen/AJS and BNP inputs
on this tensor-cohomology space and derives the former function-space
inputs using `h1Equiv`. The two input formulations are proved equivalent
(`andersen_iff_function`, `bnp_iff_function`), with precisely the same
weights, bounds, source index, and fields. Its
`not_absoluteBoundedness` corollary therefore puts the proved comparison
on an explicit path to the final counterexample statement.

## The remaining cited theorem

The primary source is Jantzen, *Representations of Algebraic Groups I*,
SFB/MPI 85-9 (1985), §§4.14–4.16, especially Proposition 4.16.
It proves that the regular cochains `A ⊗ k[G]^{⊗n}` compute derived
rational cohomology. The new Lean comparison supplies precisely the
degree-zero/one/two tensor complex needed for its `H¹` specialization.
Jantzen I.2.8 also explains the relation between rational point actions
and comodules over an algebraically closed field; the finite-dimensional
action, intertwiner and submodule comparisons above are now proved in Lean.

The proofs of Jantzen's derived-functor comparison, Andersen/AJS, BNP,
Steinberg's highest-weight and restriction theorems, and the general
simplicity theorem remain cited external results. The code does not turn
these literature hypotheses into new axioms or claim to have formalized
their original proofs.

## Verification

The comparison modules and their final transfer corollary build with:

```sh
lake build Guralnick.CoordinateLiteratureTransfer
lake env lean reports/rational-coordinate-check.lean
```

The second command checks the principal proof axioms and prints the exact
Andersen and BNP interfaces. Its saved output is
`reports/rational-coordinate-axioms.txt`; it contains only `propext`,
`Classical.choice` and `Quot.sound`. The identity-value cocycle check and
the empty-matrix boundary case are proved in `RationalCoordinateH1.lean`.
An independent second-agent review checked the tensor order/signs, the
determinant reducedness argument, invariant subspaces, and the unchanged
literature hypotheses.
