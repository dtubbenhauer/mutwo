# Explicit literature inputs

Updated 2 November 2026. This file lists the **mathematical hypotheses** of
the formalization, not new Lean axioms. The structures below are ordinary
theorem arguments. Their existence is not proved by this project. A citation
does not cause Lean to import its proof.

The new field-level ledgers reproduce the actual input statements and
their source/convention conversions:
[affine and Schur fields](audit-framework-inputs.md) and
[cohomological fields](audit-updated-transfer.md).
The [updated-manuscript comparison](audit-updated-manuscript.md) distinguishes
the proved main argument, cited background and unformalized examples.
The representation interface proves the paper's eventual-prime conclusion;
it does not separately formulate transfer at every smaller prime for which
the character formula might independently be known.

**Stricter boundary.** The finite flag counts, four polynomial coordinate
formulas, KL inversion and diagram invariance, proper-parabolic longest
existence, finite-source reversal, symmetrizer eigenvalues and absorption,
integral merge existence, cyclic block lengths, and the entire parabolic-law
bundle are now proved and removed from the final
assumptions. See [audit-elementary-inputs.md](audit-elementary-inputs.md).
The full-to-partial convolution normalization and the remaining explicit
matrix-dimension identity are now also proved. The final affine web bundle
has only two fields: canonical refinement span and full-flag orbit/Hecke
realization. Canonical Schur support follows from refinement and elementary
Hecke eigenvector arguments. Bar involutivity, nontriviality of the family's
finite action, and the separate Andersen H¹ finiteness clause have also been
removed as assumptions; the precise reductions appear below.

The final executable interfaces are `Hecke.Theory`, `PolynomialWebLiterature`,
and `CoordinateLiteratureTransfer.Inputs`. Proved conversions supply the
earlier `WebLiterature` and `LiteratureTransfer.Inputs` interfaces. `Guralnick/AxiomAudit.lean` prints those interfaces
and the final theorem types. The original family, gallery bijections, counts,
canonical corrections and row-sum calculation are separate Lean proofs;
none is a field of these literature bundles.

This ledger records the hypotheses consumed by the current proof, not a
claim that every field is logically independent or minimally quantified.
The web row identity uses the Hecke and web inputs; the five representation
inputs enter only its cohomological application. See
[audit-input-necessity.md](audit-input-necessity.md) for the actual consumers,
proved redundancies, and weaker scopes sufficient for different conclusions.

## Coxeter and Hecke framework

| Lean input | Assumed statement and source |
|---|---|
| `Hecke.WindowCoxeter` | The actual sum-zero periodic window group has the cyclic affine type-A Coxeter system; actual generator windows and inversion-count length. The adjacent-entry descent test is now derived from that sum, not assumed. Björner–Brenti, *Affine Permutations of Type A*, Propositions 3.1–3.3. |
| `Hecke.KLRealization` | The presented Hecke algebra has its reduced-word standard basis, semilinear bar, and bar-invariant Bruhat-triangular canonical basis; ordinary polynomial normalization. Kazhdan–Lusztig (1979). |
| `Hecke.PositivityInput` | Nonnegative ordinary canonical-to-standard coefficients and canonical multiplication structure constants, for the entire Coxeter system. Elias–Williamson, Corollary 1.2(1),(2). |

Sources: [Björner–Brenti](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v3i2r18/pdf/),
[KL](https://doi.org/10.1007/BF01390031),
[Elias–Williamson](https://annals.math.princeton.edu/wp-content/uploads/annals-v180-n3-p06-p.pdf).

The algebra itself is a quotient of the free algebra by braid relations and
`(H_s-v^-1)(H_s+v)=0`; it is not defined by a desired coefficient array.
`Q=v^-2`, SSW's `q=v`, and Cui's parameter is `v^-1`. Lower canonical
coefficients are in `v Z[v]`. Ordinary, trivial-induced spherical and
sign-induced antispherical coefficients are not interchanged. The added
`FidelityKL` proofs establish uniqueness of the standard basis, bar,
canonical basis and polynomials for a fixed Coxeter model satisfying this
interface. They do not construct a realization or discharge the remaining
external assumptions.

Bar involutivity is no longer a field of `Hecke.KLRealization`.
`KLDerivedBar.bar_involutive` expands an arbitrary element in the canonical
basis, applies the scalar-inverting bar twice, and uses that bar fixes each
canonical basis element. The other stated KL realization data remain inputs.

## Parabolic, affine Schur and lattice framework

These are the fields of `PolynomialWebLiterature` and their lower-level
interfaces. Each ranges over arbitrary
appropriate parabolics, compositions, affine indices, fields or vector
spaces, before the special six-map word is selected.

| Field / interface | Exact scope and source |
|---|---|
| `refinement : CanonicalRefinement.StandardCompatibility` | A canonical basis element maximal in a double coset belongs to the span of the corresponding normalized double-coset sums. Williamson §2.3, (2.3.1), directly for arbitrary finitary parabolics; Cui Lemma 3.1, Theorem 3.1, equations (3.4)–(3.5) for the affine Schur dictionary. The coordinate ratio under refinement is proved in Lean. |
| `full_flag : FullFlagHeckeConvolution.Input` (at each prime) | Full-flag orbit classification in the balanced component and binary affine Hecke convolution on literal polynomial lattices. Lusztig §§1.3–1.9, especially Lemmas 1.4–1.5 and §1.7; Cui §7.1, Lemma 7.1. The input contains no partial flags, Poincare factors or arbitrary-chain formula. |

The complete matrix dimension/length dictionary is now derived from
actual inversion counts in `OrbitDimensionLength`. Du–Fu and the dimension
result in Cui remain background references, not additional formal inputs.

Sources: [Cui](https://arxiv.org/html/1407.4557v3),
[Du–Fu](https://arxiv.org/abs/1311.1868),
[Williamson, corrected version](https://arxiv.org/pdf/1010.1283v3)
and [erratum](https://doi.org/10.1093/imrn/rnae007),
[BLM](https://doi.org/10.1215/S0012-7094-90-06124-1),
[Lusztig](https://doi.org/10.4310/AJM.1999.v3.n1.a7),
[Vinroot](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v19i3p5/pdf/)
(background only: its counting formulas are now proved internally).

**Three former assumptions are now proved.** `ParabolicWeb.scalar_ne_zero`
evaluates the actual finite Poincaré sum at `v=1`.
`ParabolicWeb.Laws.scalar_bar` derives bar invariance from the existing
absorption identity and the canonical basis. `LaurentLattice.interval_lift`
constructs an actual full `k[[t]]`-lattice from any vector subspace in the
one-period interval; it requires no `LaurentLattice.Theory` input. These
three properties have been removed from the input structures. See
[audit-assumption-reduction.md](audit-assumption-reduction.md).

**The general lattice-theory input is now discharged.** The four remaining
facts of `LaurentLattice.Theory`—finite relative quotients, the signed-degree
difference formula, period dimension, and period finiteness—are proved from
the actual finitely generated full power-series modules. `provedTheory`
constructs the bundle for every field and ambient dimension. The
`GeneralLatticeFlagInput.lattice_theory` field was removed; its retained
method name returns that proof. Finite-flag enumeration is now also proved;
the historical `GeneralLatticeFlagInput` structure has no fields. See [audit-lattice-completion.md](audit-lattice-completion.md).

The finite-quotient comparison `k[t]/(t^d) ≃ k[[t]]/(t^d)` is now part of
the proved global completion/algebraization equivalence. The subsequent
proofs preserve actual relative quotient spaces, degree, shifts, all retained
flag masks, galleries and the orbit-coordinate quotients. Polynomial
lattices also satisfy the literal basis condition in Lusztig's definition,
by `PolynomialLattice.exists_basis_extending`.

**Source-model inputs and normalization.** `PolynomialWebLiterature` now
states the geometric inputs on actual polynomial Laurent lattices.
Its `toWebLiterature` conversion proves the passage to the completed model,
including the absolute-degree and arbitrary-mask flag conditions. No
completion hypothesis occurs in the new bundle. See
[audit-model-comparisons.md](audit-model-comparisons.md).

The full-flag realization is the remaining convolution theorem. Its
standard kernel is defined from the actual Hecke coordinates and literal
full-flag relative position. The parabolic indicator, full-refinement
existence, fiber cardinality, configuration bijection, arbitrary-chain count
and exponent conversion are separately proved. The actual integral cleared
identity supplies the normalization; the old partial-gallery input is
constructed by `PolynomialConvolutionConstruction.fromFullFlag`. See
[audit-full-flag-normalization.md](audit-full-flag-normalization.md).

**Canonical Schur support is now derived from refinement.**
`SchurCornerEigen` proves that the normalized double-coset standard sums
satisfy the spherical eigenconditions. `HeckeEigenCoordinates` proves that
every maximal-length index in an eigenvector's canonical expansion has the
required left and right descents. Refinement therefore puts the corresponding
canonical element in the same corner; subtracting it and inducting on finite
support gives `CanonicalSchurFromRefinement.toCompatibility`. This argument
uses neither positivity nor convolution. The final bundle no longer contains
`schur_product`; its `schur` method returns this proof from `refinement`.
The earlier `CanonicalSchurEigenReduction` conversion remains a historical
alternative conditional on product support, not an additional final input.

Williamson directly covers the arbitrary-finitary **algebraic** corner and
refinement statements; no simultaneous cyclic conjugacy is assumed.
No special-family coefficient equality is included in these inputs.

**Web presentation qualification.** SSW's integral q-web realization
(Theorem 3.9, (3.21)–(3.24), Theorem 4.16, Proposition 4.18(1),
[arXiv:2504.10270v1](https://arxiv.org/pdf/2504.10270v1)) explains the diagrammatic
interpretation. The formal proof uses the manuscript's direct six integral
parabolic module maps. It does not require or claim a formalized equivalence
of the entire annular web presentation with the Schur category. The graph,
ordered ports, ribbon orders, thicknesses, winding data and its parabolic
boundary masks are defined independently. The specific bridge is now a
proved theorem: `WebTraceEvaluation.family_graph_evaluation_eq_raw`,
strengthened to full module-map equality in `WebProof.graph_morphism_eq_sixMaps`.
It follows from checked graph replay, absolute-position recuts and proved
composition of the same local integral maps. No graph-specific equality
or extra assumption was added to this literature ledger. The evaluation
is for the fixed checked presentation; global isotopy independence and
the full SSW rotation/dot functor remain outside this construction. See
`graph-evaluation.md`. Elementary web basis and
canonical basis are kept distinct. SSW's generic thin-dot presentation must
not be substituted for the integral construction.

## Algebraic groups and first cohomology

`CoordinateLiteratureTransfer.Inputs T` contains the following five explicit
general inputs; its proved conversion supplies the original function-cochain
interface. Here `N=2m+1`, `m>=2`, and `k=algebraic_closure(F_p)`.

1. **`HighestWeightExistence`.** Every dominant p-restricted root-lattice
   weight has a simple rational highest-weight module. The Lean predicate
   uses an actual finite-dimensional representation of `SL_N(k)`, a
   nonzero highest-weight vector, torus character, upper-unipotent invariance,
   irreducibility, and polynomial matrix coefficients. It is not a dimension
   placeholder. Source: highest-weight classification, e.g. Jantzen/Steinberg.
2. **`AndersenAJS T`.** For each rank there is a threshold `p0`; for every
   prime `p>=p0`, `p>N`, every dominant p-restricted weight `lambda=b dot_p 0`
   with `b` finite-left-minimal, and every corresponding simple module,
   the `finrank` of coordinate `H^1` equals the coefficient of `v` in the
   ordinary canonical coefficient with **source `w0`** and
   target `w0*b`. This combines the eventual character formula, Andersen's
   degree-one Weyl-to-simple formula with Weyl source `V(0)=k`, the general
   spherical dictionary, and regular-cochain computation of rational H^1.
   Sources: AJS §§16.1, 16.24 and the quantum/affine character results invoked in its introduction; Andersen (1986); Lübeck Theorems 3.1 and 4.5; Jantzen's
   1985 preprint §§4.14–4.16, Proposition 4.16.
   The separate finite-dimensionality conjunct has been removed from both
   coordinate and function-cochain interfaces. Actual finite-group H¹ is
   proved finite-dimensional in `FiniteCohomology`; BNP transports this fact
   to the coordinate/rational model in its characteristic range. The
   equality-only Andersen statement alone is not claimed to recover the old
   finiteness clause outside that range.
3. **`BNP`.** For `p>=5(N-1)`, and every such restricted principal-block
   highest weight, rational H^1 and H^1 of the same module restricted to
   `SL_N(F_p)` are linearly isomorphic. This is the specialization
   `s=1, r=1, nu=0, i=1` of Bendel–Nakano–Pillen §7.5. The actual dot label
   lies in the root-lattice affine subgroup of the theorem's extended
   affine group. **Only existence of an isomorphism is assumed:** the
   checked theorem does not identify it with a specified cocycle map.
4. **`Steinberg`.** A p-restricted simple highest-weight module restricts
   irreducibly to `SL_N(F_p)`. Source: Steinberg (1963), §§6.1, 7.4;
   §7.6 supplies the central-quotient context. The former nontriviality
   conjunct is removed: `HighestWeight.family_restrictPrime_nontrivial`
   proves nontrivial action for every displayed family member from its
   highest-weight vector and an explicit finite diagonal element, throughout
   `m>=2`, `1<=j<=m`, `p>N`.
5. **`PSLSimplicity`.** `PSL_N(F_p)` is simple in the range `m>=2`,
   `p>=5(N-1)`, avoiding the small exceptions. Source: Steinberg's Yale
   notes, §4, Theorem 5.

Sources: [AJS](https://www.numdam.org/item/AST_1994__220__1_0/),
[Andersen](https://doi.org/10.1016/S0001-8708(86)80008-1),
[Lübeck](https://arxiv.org/html/1610.07055v2),
[Jantzen, 1985 preprint](https://archive.mpim-bonn.mpg.de/id/eprint/607/1/preprint_1985_9.pdf),
[BNP](https://doi.org/10.1016/S0022-4049(01)00024-X),
[Steinberg 1963](https://doi.org/10.1017/S0027763000011016),
[Steinberg Yale notes](https://www.math.utah.edu/~ptrapa/math-library/steinberg/steinberg-yale-notes.pdf).

Source-checking limits: the original AJS monograph, Jantzen preprint,
BNP §7.5, Steinberg 1963 and the Yale simplicity theorem have now been
recovered and checked at the indicated locations. AJS §16.24 supports the
root-system-dependent threshold in the restricted region; it supplies a
modular/quantum comparison, not directly the displayed H^1 identity.
Andersen's original full text remains inaccessible, so the degree-one Ext
formula and exact source/normalization conversion are still checked through
Lübeck rather than independently certified from Andersen. The follow-up
[audit](audit-andersen-followup.md) locates the original targets more
precisely at §2, Propositions 2.8 and 2.12, using accessible papers by
Andersen; their quantum/category O analogues are not substitute assumptions.
The polynomial-function/coordinate-algebra comparison is now proved:
the determinant ideal is radical, its quotient is identified with actual
polynomial functions over an algebraically closed field, and the action,
comodule, invariant-subspace and degree-one cohomology models agree.
`CoordinateLiteratureTransfer` states Andersen/AJS and BNP on the genuine
coordinate tensor complex and derives the earlier inputs through the
proved `h1Equiv`. The two input formulations are proved equivalent.
See [audit-rational-coordinate-comparison.md](audit-rational-coordinate-comparison.md).
The proof that the regular complex computes derived rational cohomology
remains Jantzen's cited Proposition 4.16. It is the shared interpretation
used by Andersen and BNP, not a sixth representation field or two independent
assumptions. See
[audit-primary-transfer.md](audit-primary-transfer.md) for the precise
comparisons, checked pages and source provenance. Jantzen's Proposition
4.16 refers to the linked 1985 preprint, not the later edition. These source
audits do not prove the literature interfaces in Lean.

The threshold `p0` may depend on rank. The BNP bound alone does not certify
the character formula. No claim is made for a fixed characteristic as rank
increases, or for every small prime.

The universal label and prime quantifiers state convenient sufficient
theorems. The named row uses only its `m` displayed weights at a common
eligible prime; eventual bounds for these finitely many indices can be
combined. Bare negation of absolute boundedness needs only an unbounded
sequence of ranks with one large-coefficient member and one suitable prime
at each rank. Faithfulness is still part of that conclusion, so the current
use of PSL simplicity does not disappear when the named row is omitted.

## What is proved after supplying those inputs

The paper's weight is proved equal to `u_(j;m)^-1 dot_p 0`, dominant,
restricted, regular and nonzero for `p>N`. The modules are selected by
these actual highest weights. Their central action is proved trivial from
the root-lattice torus character; the center order is proved invertible;
central inflation gives an actual H^1 linear equivalence. The family's
nontriviality is proved directly in `FamilyNontriviality`: the determinant-one
diagonal element with minus signs at coordinates `m-1` and `m` has
highest-weight character `-1`. The corresponding weight coordinates are
`(1,0)` for `j<m` and `(p-2,0)` for `j=m`, with `p` odd in the stated range.
Finite-group simplicity and this proved nontriviality yield faithfulness.
Absolute irreducibility
over the algebraic closure is proved using actual scalar extension, and
finite-dimensionality of finite-group H^1 is proved.

Consequently the application uses the fixed trivial source throughout.
It does not pass from arbitrary-pair Ext^1, antispherical coefficients, or
ordinary coefficients with lower endpoint `e`. The actual ordinary KL
coefficient is connected to the actual named module's cohomology dimension.

The current assembly status and endpoint are in `status.md`; it distinguishes
completion modulo these inputs from an unconditional Lean theorem whose
inputs have themselves been proved.
