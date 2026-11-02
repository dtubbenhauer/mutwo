# Primary-source audit of the affine framework

**Current status:** this is a historical source audit. The completion,
degree, coordinate, full-refinement, fiber-count, partial-gallery
normalization and matrix-dimension obligations discussed below are now
proved in Lean. Only the source-level full-flag orbit/Hecke theorem remains
external on the convolution side. See
[audit-full-flag-normalization.md](audit-full-flag-normalization.md) and
[audit-elementary-inputs.md](audit-elementary-inputs.md).
`literature-inputs.md` is the current assumption ledger.

30 October 2026. This audit reads the actual interfaces in `WebLiterature.lean`,
`FlagConvolution.lean`, `OrbitMatrix.lean`, and `OrbitLengthInput.lean`. It does
not construct their inhabitants in Lean. No manuscript or Lean source was
changed by this audit.

The main improvement is an exact source for **all finitary parabolics**:
Williamson's corrected *Singular Soergel bimodules*, §2.3, directly covers the
algebraic corner and refinement interfaces, including parabolics containing
the affine generator. There is no need to justify those two interfaces by
an unspecified conjugacy extension of Cui. The geometric comparison with
completed lattices is still a separate obligation; Lusztig's original 1999
paper does not literally supply a completed-lattice statement.

## Sources actually checked

The retained originals and hashes are listed in
[`literature-audit/affine/provenance.json`](literature-audit/affine/provenance.json).

- [Williamson, corrected version, arXiv:1010.1283v3](https://arxiv.org/pdf/1010.1283v3):
  §2.1, Proposition 2.1.1; §2.2, (2.2.1)–(2.2.4); §2.3, Definition 2.3.1,
  Remark 2.3.2, the paragraphs surrounding (2.3.1), and Proposition 2.3.3.
  Printed pp. 9, 11–14. This is the version incorporating the erratum.
- [Cui, arXiv:1407.4557v3](https://arxiv.org/html/1407.4557v3): §2.5,
  Lemma 2.1; §3, Lemma 3.1, Theorem 3.1 and (3.4)–(3.5); §7.1,
  Lemma 7.1; §7.2, Lemma 7.2. The local PDF/text is in `RevisedWeb/references`.
- [Du–Fu, arXiv:1311.1868](https://arxiv.org/pdf/1311.1868): §2,
  pp. 4–5, the block intervals and the **unnumbered** bijection immediately
  before (2.0.3), followed by the dimension sum in (2.0.3). The block-count
  bijection is not equation (2.0.1); references identifying it that way
  should be corrected.
- [Lusztig, *Aperiodicity in quantum affine gl_n*, author copy](https://math.mit.edu/~gyuri/papers/aper.ps):
  §§1.2–1.9, Lemmas 1.4–1.5, §1.6(a), §4.1 and Lemma 4.3.
  The author-copy pagination differs from the published pp. 147–177.

BLM is background for the finite construction. It is not, by itself, a source
for the affine completed-lattice assertion.

## Statement-by-statement coverage

| Actual Lean input | Source coverage and remaining work |
|---|---|
| `WebLiterature.parabolic` | Williamson (2.2.2)–(2.2.4) gives finite symmetrizers, eigenvalues and absorption for every finitary subset, in the same `v` convention. §2.3 gives integral parabolic composition. These are general framework results; the specific six-map word is not imported. |
| `CanonicalSchur.Compatibility.canonical_support` | Williamson §2.3, printed p. 13, gives a canonical basis of the whole corner indexed by maximal double-coset elements. This directly implies the stated support condition for every vector of that corner. |
| `CanonicalRefinement.StandardCompatibility.canonical_span` | The same page gives the weighted standard double-coset sums and (2.3.1), then expands each canonical corner element in that basis. This directly covers arbitrary finitary `I,J`, including cyclic facets. |
| `FlagConvolution.Input.realization` | Realize the target by coordinate lattices and the source by the actual balanced monomial window. Checking the fixed degrees is an elementary lattice calculation. The underlying orbit framework is Lusztig Lemma 1.5; the completed version still requires the comparison below. |
| `FlagConvolution.Input.finite_gallery` | Lusztig §1.7 supplies finite two-step convolution fibers in the polynomial model. Arbitrary finite chains follow by convolution or by the uniform boundedness argument below. The complete-to-partial fiber correspondence must be checked for the actual retained masks. |
| `FlagConvolution.Input.specialization` | Cui Lemma 7.1 supplies the orbit/Hecke algebra identification. The exact exponent and arbitrary-chain formulation are derived below, not a literal quotation of that lemma. Completion and the degree-zero component remain explicit comparison steps. |
| `CoordinateDimensionInput.block_finite`, `.block_dimension` | Lusztig Lemmas 1.4–1.5 identify intersection subquotients; Du–Fu's block bijection identifies the monomial-window entries. The actual completed coordinate realization requires the elementary truncation/coordinate comparison below. |
| `.cumulative_finite`, `.cumulative_dimension` | Consequences of the same finite coordinate intervals, using the subset of row indices whose inverse image lies below the source cut. These are not separately numbered theorems in Cui. |
| `.source_le_target`, `.target_le_source` | Coordinate containment tests: every included coordinate monomial must remain below the other cut. These should ultimately be proved directly from the independent `cutModule` and `windowEquiv` definitions. |
| `ThreeColumnLengthInput.dimension_length` | Cui Lemma 7.2 gives `d(A)=length(w_max)-length(w_source)`; its preceding periodic dimension sum matches Du–Fu (2.0.3). Zero-cut positive compositions and the full spherical source lie within the cited ordinary Schur indexing. |
| `.maximal_of_dimension` | A consequence of that formula plus uniqueness of the maximum of a finite-parabolic double coset (Williamson Proposition 2.1.1). Equal matrix means the same double coset. Equality of lengths forces the window to equal its maximum. The right-descent hypothesis is harmless; it does not replace the matrix argument. |
| `.matrix_injective` | Du–Fu's matrix bijection identifies the double coset, and uniqueness of its maximum identifies the two elements. Three-column support ensures the finite array contains the entire periodic matrix. |

The last three assertions concern actual windows and finite combinatorial
matrices. They do not need an additional completed-lattice hypothesis merely
because one proof of the length formula is geometric.

## Parameter and endpoint calculation

Write `Q` for the finite-field size and reserve `v` for Lean's parameter.
Let `T_w` denote the unnormalized Hecke basis with
`(T_s+1)(T_s-Q)=0`. Then

\[
Q=v^{-2},\qquad H_w=v^{\ell(w)}T_w,\qquad
C_I=v^{\ell(w_I)}x_I,\qquad
x_I=\sum_{a\in W_I}T_a.
\]

Set `P_I(Q)=sum_(a in W_I) Q^length(a)`. Lean's Poincaré scalar is
`h_I=v^length(w_I) P_I(Q)`. For a chain
`I_0,...,I_r`, put `R_a=I_(a-1) intersection I_a`. The cleared identities
already proved in `CanonicalChains.lean` give, after specialization where
the positive integers `P_R(Q)` can be divided,

\[
\operatorname{raw}=
v^{\omega}\frac{x_{I_r}\cdots x_{I_0}}
 {\prod_{a=1}^{r}P_{R_a}(Q)},\qquad
\omega=\ell(w_{I_0})+
\sum_{a=1}^{r}\bigl(\ell(w_{I_a})-\ell(w_{R_a})\bigr).
\]

In complete-flag convolution, `x_I` indicates agreement at the vertices
retained by `I`. The numerator counts full-flag lifts of the gallery.
Each common refinement of type `R_a` has `P_(R_a)(Q)` full-flag lifts.
Consequently the quotient counts exactly the partial galleries in Lean.
Changing the coefficient from `T_w` to `H_w` gives

\[
[H_w]\operatorname{raw}
=v^{\omega-\ell(w)}\,
\#\operatorname{Gallery}(\text{source},\text{target}).
\]

This explains the exact `Chain.weight - length(w)` exponent. It holds for
**all** `w`, not just double-coset maxima: the unnormalized characteristic
function is constant on a double coset, whereas the normalized `H_w`
coefficient changes by `v^(-length(w))`. Thus the universal quantifier in
`specialization` is not a detected overstrength. Setting `Q=p²` gives
`v=1/p`, exactly as in the interface. The target is the left endpoint and
the source is the right endpoint; no inversion or sign-induced convention
is inserted in this calculation.

## The precise completion comparison

The introduction of Lusztig's paper mentions a power-series field, but its
**definition in §1.3 uses** `k[t,t^-1]` and `k[t]`. It is therefore incorrect
to cite §1.3 as a literal definition of Lean's `k((t))`/`k[[t]]` model.

Here is a concrete replacement for the vague phrase “standard comparison.”
This is a mathematical proof outline, **not a Lean theorem in this project**.
Let `P=k[t]`, `O=k[[t]]`, and take integers `a<=b`.

1. The natural map
   `t^a P^N / t^b P^N -> t^a O^N / t^b O^N`
   is an isomorphism of `k[t]`-modules: truncate each coordinate to powers
   `a,...,b-1`. Both sides have the same displayed finite basis.
2. A lattice in that interval is the inverse image of a `t`-stable subspace
   of this quotient. The polynomial inverse image contains `t^b P^N`, is
   a finite free full-rank `P`-module, and becomes all `k[t,t^-1]^N` after
   inverting `t`. Its basis therefore satisfies Lusztig's lattice condition.
   The completed inverse image is an actual full `O`-lattice. These inverse
   images are exchanged by completion.
3. The correspondence preserves inclusions, intersections, sums, powers of
   `t`, and all relative quotient dimensions. In particular it preserves
   the project's signed degree relative to the standard lattice.
4. Every full completed lattice admits such bounds, by finite generation
   and spanning. For a fixed finite collection use common bounds. The
   correspondences agree when the bounds enlarge, so they apply to periodic
   flags and their finite incidence configurations without choosing a
   different lattice for each bound.

For a gallery of `r` steps one can use common bounds depending only on one
fixed endpoint and `r`. Inside a periodic flag, any node lies between `t`
times and `t^-1` times any other node. At a chain step the refinement retains
vertices from both adjacent boundaries. Each step therefore changes a
coarse bound by at most one period. All choices lie in one finite quotient,
which also proves finiteness over a finite field. The argument applies
whether or not a boundary retains the cut zero.

For `CoordinateDimensionInput` one can work even more directly. First
remove the common Laurent-linear map `g`, which preserves subquotient
dimensions and containment. The remaining lattices are diagonal monomial
lattices, so their subquotients have a basis indexed by the indicated finite
integer intervals. The `N+a` offset in `cutLevel` shifts both target and
source cuts by one period and cancels because `w(i+N)=w(i)+N`.

These observations give an explicit route to formalizing the comparison;
they do not remove any current Lean hypothesis by themselves.

## Cyclic cuts and the affine subgroup

An arbitrary pair of finitary parabolics need not be simultaneously rotated
into subsets of the finite nodes. Consequently “conjugate to ordinary
compositions” is not a sufficient explanation for an entire mixed chain.
For the **algebraic** assertions, Williamson's arbitrary-Coxeter statement
avoids that issue completely.

For the **flag** assertion, use one space of complete periodic flags and
forget the omitted vertices separately at each object. The exact remaining
lemma is:

> For every proper mask `I`, forgetting to `retained I` is onto the actual
> degree-normalized partial flags, its fibers have cardinality `P_I(Q)`,
> and relative position of two complete lifts in `W_I` is equivalent to
> equality of the retained partial flags. The same construction for
> `I intersection J` identifies complete lifts of a common refinement.

The fiber assertion reduces to full flags in the finite vector-space
intervals between retained lattices; a cyclic interval crossing zero is
treated by multiplying one endpoint by `t`. This supplies the gallery
interpretation used above without dropping the seam.

Cui and Du–Fu use the **extended** affine group. Lean uses its balanced
affine subgroup. To specialize the comparison, retain the component of
complete flags with degree `i` at the `i`-th node, and the Laurent-linear
changes of coordinates of determinant valuation zero. Balanced monomial
windows preserve that component; every `W_I` lies in the balanced subgroup.
Hence all the convolution factors above stay there. Forgetting cyclic
vertices must retain their **absolute degrees**, as Lean's `Flag.degree_eq`
does; simply relabelling packets and discarding the degree is insufficient.

## Conclusion and recommended ledger corrections

No false assertion was found in these particular interfaces. The audit
strengthens their source justification but is not an existence proof of the
literature structures in Lean.

1. Cite Williamson §2.3 directly for `schur` and `refinement`; remove the
   suggestion that their cyclic scope depends on a conjugacy extension of
   Cui.
2. Keep the completed-lattice, complete-to-partial flag, and degree-zero
   component comparisons explicit under `convolution`. Replace a blanket
   “standard comparison” with the exact statements above.
3. Cite Du–Fu's block bijection as the unnumbered display before (2.0.3).
4. Preserve the distinction between a primary theorem, an elementary
   consequence with the derivation supplied here, and a kernel-checked
   construction. None of these source checks is an unconditional Lean
   counterexample.


## Subsequent formal progress

The later [lattice verification](audit-lattice-completion.md) proves the
complete general `LaurentLattice.Theory` bundle, the natural finite
polynomial/power-series quotient equivalence, and the bounded actual-lattice
subspace correspondence. The subsequent global model comparison now assembles the full completion,
flags, galleries, absolute degrees and arbitrary coordinate changes. The
original canonical endpoints and winding data are preserved by proved
equalities. The source-derived normalized convolution theorem remains
explicit input. `literature-inputs.md` is the current assumption ledger.
