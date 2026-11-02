# Final review of the elementary-input boundary

**Subsequent necessity audit:** the three-field interface reviewed below has
been reduced further. `schur_product` is now proved from `refinement` by
`CanonicalSchurFromRefinement.toCompatibility`, so the final bundle has
only `refinement` and `full_flag`. The review below records the previous
boundary; [audit-input-necessity.md](audit-input-necessity.md) gives the current
assumptions and reductions.

30 October 2026. Scope: the current three-field `PolynomialWebLiterature`,
its constructed `toWebLiterature` map, and the route to
`ModelComparisonCounterexample`. The initial review was read-only and exposed the eigen-corner translation
discussed below; a subsequent explicit reduction now closes it. The review
also checked the displayed family and row theorem in `../main.tex`.
The review below distinguishes the proved deductions from the mathematical
interpretation of the remaining source-theorem interfaces.

## Finding

The final web bundle now has exactly three fields: `schur_product`, `refinement`,
and `full_flag`. Its `schur` method is a proved conversion. There is no remaining field for the matrix dimension,
finite-parabolic laws, longest elements, flag counts, lattice coordinates,
arbitrary-chain convolution, or its normalization. The source code really
constructs those former inputs; they were not merely renamed.

I found no family-specific assertion concealed in these three fields and
no change of the ordinary KL endpoint or of the cohomology source.
The resulting theorem remains conditional on the stated general literature
interfaces. The three web fields are not the complete dependency list:
`Hecke.TheoryFamily` and `CoordinateLiteratureTransfer.Inputs` are also
arguments to the final theorem.

The initially identified elementary Schur-corner translation is now
proved, as described below. The existing primary-source verification
qualification concerning Andersen remains. This review does not certify the
external interfaces themselves as Lean theorems.

## The three fields, examined literally

| Field | What the Lean premise says | What has been removed from it |
|---|---|---|
| `schur_product` | For arbitrary finitary masks and an arbitrary Hecke element `x`, the literal product `rawSum_I * x * rawSum_J` has canonical support only at double-coset maximal elements. The two raw sums are defined from ordinary standard elements before canonical compatibility. | The implication from generator eigenconditions to the required product is proved. No six-map support list, family classification, raw coefficient, or canonical correction is assumed. |
| `refinement` | Every canonical element maximal for arbitrary finitary masks belongs to the span of actual normalized ordinary-standard sums over their finite double cosets. | The standard-coordinate ratios, specific spherical shift, one-line shift, and their degree consequences are proved. |
| `full_flag` | At each prime-square field, actual full polynomial flags have unique balanced-window relative positions, and the normalized ordinary Hecke kernels multiply by binary convolution. | No partial flag, full-lift count, Poincare denominator, arbitrary-chain formula, or special endpoint formula is a field. |

The local corrected Williamson text, §2.3, explicitly gives normalized
standard double-coset sums, the maximal-index canonical basis, and both
basis descriptions for arbitrary finitary parabolics. Its parameter agrees
with the code's relation `H_s²=1+(v⁻¹−v)H_s`. Cui supplies the affine Schur
interpretation. These are general canonical-basis theorems, not arithmetic
facts about this manuscript's family.

**The eigen-corner translation is now proved.** Williamson defines the
corner as an intersection of symmetrizer ideals, while the working code's
`CanonicalSchur.corner` uses simultaneous generator eigenconditions.
The initial review identified this elementary change of formulation inside
the former `schur` field. It is no longer left there.

`CanonicalSchurEigenReduction.ProductCompatibility` assumes canonical support
only for actual products of the explicit finite standard sums. These
products already lie in the two source ideals; no eigen-corner equivalence
is required to apply the source theorem. The independent left and right
subgroup-generator induction proofs give, for every working corner vector
`x`, the literal identity

\[
\operatorname{rawSum}_I\,x\,\operatorname{rawSum}_J=(h_Ih_J)x.
\]

Both scalars are proved nonzero from their actual sums. Applying canonical
coordinates and cancelling therefore supplies the old compatibility
statement. This proof does not invoke the canonical finite-symmetrizer
formula, which is derived afterward, so it introduces no circular argument.
The passage is implemented by `CanonicalSchurEigenReduction.toCompatibility`.
The source theorem remains the general canonical basis of the intersection
of parabolic ideals, with the finite standard sums displayed in Williamson
(2.2.2). It is not an eigen-support assertion under a new name.

The two remaining Schur theorem premises still overlap mathematically;
the three-field bundle need not be a minimal independent list of major
theorems.

For `full_flag`, the local Lusztig text, §§1.3–1.5, works with polynomial
Laurent lattices and classifies periodic-flag pair orbits; §§1.7–1.10 give
finite-field convolution. The project's full-flag Hecke input is a
specialization and translation of that framework together with the
full-flag Hecke identification cited to Cui. It is not the verbatim statement
of one numbered lemma. The degree-zero restriction, balanced affine
indexing, orientation of relative position, and `H_w=v^length(w)T_w`
normalization are visible in the interface. Its truth in this exact
formulation remains an external mathematical assumption.

## The conversion actually proves the elementary steps

`polynomialLongest` constructs actual finite parabolic longest elements.
`PolynomialWebLiterature.schur` first applies the proved product-to-eigen
reduction. `polynomialParabolic` then supplies its two legacy law fields using
`ParabolicStandardSum.standard_sum` and
`ParabolicIdealInclusion.inclusion`; eigenvalues, absorption and the integral
merge are then derived. The cyclic block formula and the ordinary finite
reversal are proved separately. The final bundle no longer accepts those
facts as arguments.

The new convolution route is an actual composition of proofs:

1. `ParabolicFlagStabilizer` identifies equality of retained coordinate cuts
   with membership in the generated finite subgroup. The full-flag theorem
   then gives the normalized symmetrizer indicator.
2. Full refinements are constructed by extending a genuine finite-dimensional
   flag, lifting it in a one-period lattice quotient, and algebraizing it.
   Existence is not inferred from a presumed cardinality.
3. Squaring that indicator, together with the independently proved
   symmetrizer absorption identity, counts the actual full-refinement
   subtype. `PolynomialFullLiftCardinality.lift_card_eq` obtains its Poincare
   cardinality by cancellation of a nonzero unit.
4. `PolynomialFullGallery.configurationEquiv` is a bijection of actual
   configurations: a full chain corresponds to a partial gallery with one
   full lift of each common-facet refinement. Its cardinality therefore gives
   precisely the product of Poincare factors.
5. Binary full-flag convolution counts the actual chain numerator by
   induction. `Chain.cleared` is an identity for the actual integral maps.
   `PolynomialConvolutionNormalization` proves the scalar specialization,
   exponent identity, positivity and cancellation that recover the raw
   partial-gallery coefficient.
6. `PolynomialCanonicalFullFlags.forget_pair` retains the literal canonical
   endpoints and window. The proved completion/algebraization and coordinate
   equivalences then supply the old completed-lattice interface.

There is no assumed equality equating a numerical matrix operation with a
web or cohomology operation in this route. Intermediate conditional
normalization lemmas have their counting premises discharged by these
configuration proofs before `fromFullFlag` is supplied to the final bundle.

## Matrix formula: semantic check

`OrbitDimensionLength.dimensionLength c` proves exactly the former
`OrbitMatrixElementary.DimensionLengthInput c`, for every positive output
composition at cut zero, supported actual window, and actual double-maximal
representative. It does not replace that statement by a special-family
numerical calculation.

Write `t_i=(w⁻¹).winding i`, with `−1≤t_i≤1`. For `i<j`, right maximality
makes the source window decreasing and determines inverse residue order.
The actual affine inversion summand is

\[
1+\mathbf1_{t_i+1<t_j}+\mathbf1_{t_j+1<t_i}+\mathbf1_{t_j<t_i}.
\]

The leading `1` is exactly the contribution of the finite reversal `w₀`.
The proof uses the actual Coxeter inverse-length theorem to pass to `w⁻¹`;
it does not replace the KL pair by a different pair.

Each actual matrix entry is the cardinality of a row/column fiber of the
output residues. Expanding the products in `PeriodicMatrix.dimension`
gives ordered-pair terms

\[
\mathbf1_{t_i+1<t_j}+
\mathbf1_{\operatorname{row}(j)\le\operatorname{row}(i),\ t_i<t_j}.
\]

The packet row function is monotone. Left maximality makes inverse winding
antitone inside each row. Pairing the two orientations of distinct residues
therefore gives precisely the three extra inversion terms above; diagonal
terms vanish. This proves the identical finite dimension sum used by the
manuscript's coefficient calculation. It does not assert a new geometric
interpretation of arbitrary varieties. The separate converse and injectivity
proofs complete the old `ThreeColumnLengthInput` interface.

The actual values `−1,0,1` are identified with `Family.columnShift`; rows are
identified with the composition's actual successive partial sums. Thus no
unproved relation between histogram labels and the original matrix is
introduced. In particular `matrix_dimension` is now a theorem-valued method,
not a structure field.

## Endpoint and application remain the manuscript's statements

`Hecke.familyMu` is the coefficient at `criticalIndex m j` of the ordinary
polynomial with lower endpoint `AffinePermutation.longest (2*m+1)` and
upper endpoint `Family.upper = u*w₀`. `CanonicalRowSum.familyIndex` uses
this same upper endpoint. Neither a coefficient with lower endpoint the
identity nor an antispherical coefficient is substituted.

`ModelComparisonCounterexample.row_sum` concludes
`sum(j=1..m) mu_(j;m) = choose(m+1,2)`. This matches the manuscript's theorem;
it does not claim the conjectural individual formula `mu_(j;m)=j`.
The named cohomology theorem retains the module family, the two separate
large-characteristic requirements, and the lower bound `m/2+1`, which is
`ceil((m+1)/2)` for integral `m`.

The application takes `b=u⁻¹` and proves the actual inverse-dot highest
weight label and finite-left-minimal condition. The external cohomology
interface uses the coefficient `[v]h_(w₀,w₀*b)`. Proved simultaneous KL
inversion changes that pair to `(w₀,u*w₀)`, preserving the trivial-source
interpretation. Rational-to-finite cohomology, restriction irreducibility,
and the simple quotient are supplied by their explicitly listed literature
inputs and the proved central-descent/model-comparison steps.

`AbsoluteBoundedness` quantifies one bound over all fields, finite groups,
and faithful finite-dimensional absolutely irreducible representations.
The witnesses lie in `PSL_(2m+1)(F_p)` over `overline(F_p)`, with primes
large enough for the rank-dependent character-formula threshold as well as
`p≥5(2m)`. Failure in this subclass negates that all-field conjecture. There
is no claim of a fixed characteristic as rank grows.

## Literature and trust qualifications

The endpoint theorem still receives `Hecke.TheoryFamily`, containing the
actual affine Coxeter realization, ordinary KL realization and general
positivity, as well as the three web fields and the five representation
inputs. A statement saying that only the three web references remain would
omit essential hypotheses.

The `AndersenAJS` field is itself a combined source-level statement: eventual
characters, the degree-one Weyl-to-simple Ext formula with Weyl source
`V(0)=k`, the spherical/ordinary normalization, and computation of rational
cohomology by the regular complex. It is not literally AJS Corollary 16.24.
The coordinate-to-function cochain comparison is now proved, but Jantzen's
identification of the regular complex with derived rational cohomology is
still part of the cited input interpretation.

The existing Andersen follow-up explicitly records that the original 1986
full text has not been inspected; §2, Propositions 2.8 and 2.12 have been
located through later original-author references. Lübeck's fixed-Weyl-source
formulation supports the use made here. Quantum and category-O analogues
are not replacements. This review did not close that primary-source check
and found no reason to conceal it or recast it as an established Lean
result.

The new normalization, lift-cardinality, matrix and eigen-corner reduction
modules passed their
targeted `lake build` checks. Their principal `#print axioms` outputs contain
only `propext`, `Classical.choice`, and `Quot.sound`. These outputs verify
proof integrity relative to the explicit theorem parameters; they do not
prove those external parameters exist. This read-only review did not rerun
the complete project verification. The current full-project run and counts
should be taken from the final verification report rather than older status
paragraphs.

The supported conclusion is a faithful conditional proof of the manuscript's
row-sum and counterexample statements from the displayed source-theorem
interfaces. It is not an unconditional machine-checked counterexample, nor
a completed independent primary-source certification of every interface.
