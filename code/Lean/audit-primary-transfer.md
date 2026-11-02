# Primary-source audit of the cohomology transfer

30 October 2026. Scope: `LiteratureTransfer.lean`, `RationalCohomology.lean`,
`HighestWeight.lean`, and the application in `../main.tex`. This audit changes
no Lean declaration and no manuscript text.

Subsequent formalization has closed the polynomial-function/model comparison
described below. The exact coordinate ring, action/comodule equivalence,
invariant subspaces, and regular tensor H¹ comparison are now proved; see
[audit-rational-coordinate-comparison.md](audit-rational-coordinate-comparison.md).
The source-access qualifications about Andersen remain as recorded here.

The original AJS monograph has now been recovered and checked, removing one
specific limitation of the earlier source audit. Jantzen's original cochain
comparison, BNP's original finite-group comparison, and Steinberg's original
restriction theorem were also checked. **The original Andersen 1986 Ext
formula has still not been inspected.** Its precise degree-one formulation
remains checked through Lübeck. No contradiction with the current transfer
interfaces was found, but this is not a completed primary-source certification
of `AndersenAJS`.

Downloads, extraction instructions, page images and SHA-256 provenance are
in [literature-audit](literature-audit/). This is a mathematical source audit,
not another kernel verification of the external theorems.

## What was checked

| Lean input or comparison | Original source checked | Finding |
|---|---|---|
| Rank-dependent eventual characteristic bound | AJS §§16.1, 16.22–16.24, especially printed p.229 | Restricted labels permit a bound depending only on the root system. The original result compares modular and quantum characters; the KL character theorem also uses the quantum/affine results discussed in the introduction. |
| Rational `H¹` as regular crossed homomorphisms | Jantzen 1985 I, §§4.14–4.16, printed pp.77–79 | The cochain differential and coboundaries agree. Identifying the code's evaluated polynomial functions with scheme-theoretic regular maps remains an external model comparison. |
| `BNP` | BNP §7.5, printed p.141 | The exact prime-field specialization has the required source, module and characteristic bound. |
| `HighestWeightExistence` and `Steinberg` | Steinberg 1963 §§2.7, 4.7–4.9, 6.1, 7.4–7.6, printed pp.36, 41–46 | Existence, restricted irreducibility and separation of weights support these interfaces. |
| `PSLSimplicity` | Steinberg's Yale notes, §3 and §4 Theorem 5, printed p.47 | The adjoint **Chevalley group** is the central quotient used here; it must not be replaced by all rational points of the adjoint algebraic group. |
| Andersen's KL-to-Ext formula | Original publisher metadata recovered, full text inaccessible | The original theorem number, region and convention conversion are not independently certified here. Lübeck Theorem 4.5 supports the exact degree-one statement used. |

## AJS: the quantifiers and what its theorem actually supplies

The [original monograph](https://www.numdam.org/item/AST_1994__220__1_0.pdf)
is now saved as `AJS1994.pdf`. Section 16.1 fixes the root system, takes
`p>h`, and identifies its abstract affine Weyl group with the `p`-scaled
reflection group. Section 16.24 compares Weyl-module composition
multiplicities with their quantum analogues. Its restrictedness condition is
on the highest weight of the **Weyl module**, the unprimed index `w` in that
corollary. Remark 1 says that without restrictedness the bound may additionally
depend on `w`. See [the checked page](literature-audit/AJS1994-p229.png).

The introduction, printed p.5, explains that the quantum character formula
uses Kazhdan–Lusztig's equivalence and the affine character result of
Kashiwara–Tanisaki. Thus `AndersenAJS` is not the verbatim statement of
§16.24. It bundles the eventual character formula with other results; its name
must not suggest that AJS directly proves the particular `H¹` equality.

The current order `∀ m, ∃ p₀, ∀ p≥p₀, ∀ restricted labels` is consistent with
this restricted-region framework. An effective value of `p₀` is not supplied.
The separate inequality `p≥5(N−1)` in the implementation belongs to BNP and
does not establish the character formula.

## Jantzen: regular cochains versus the code's polynomial functions

Jantzen's [1985 preprint](https://archive.mpim-bonn.mpg.de/id/eprint/607/1/preprint_1985_9.pdf),
§4.14, defines `Cⁿ(G,M)=M⊗k[G]^{⊗n}` and interprets it by regular maps.
The first differentials give `a ↦ (g ↦ ga−a)` and
`f ↦ ((g,h) ↦ gf(h)−f(gh)+f(g))`.
Proposition 4.16 identifies this cohomology with derived rational cohomology.
The [differential page](literature-audit/Jantzen1985-I-p78.png) and
[comparison page](literature-audit/Jantzen1985-I-p79.png) were inspected
visually because the PDF text extraction loses formulas.

In Lean, `RationalH1` is already the regular-cocycle quotient with precisely
those boundaries. However, `regularMaps` is defined by polynomial evaluation
on the **actual matrices in `SL_N(k)`**, rather than by coordinate-ring or
group-scheme morphisms. The remaining comparison needs the following facts:

1. For algebraically closed `k`, regular functions on the smooth affine
   variety `SL_N` are polynomial functions in its matrix entries, with
   coordinate ring `k[x_ij]/(det−1)`.
2. Evaluation on algebraically closed points is faithful for these reduced
   varieties, also for `SL_N×SL_N`. Consequently the pointwise group-action
   and cocycle identities are identities of regular maps.
3. In finite dimension, these regular matrix coefficients give the usual
   rational representation, and invariant linear subspaces agree in both
   descriptions.

These are external algebraic-geometric comparisons, not consequences of the
existing `regular_iff_coordinates` lemma alone. They are appropriate for the
actual coefficient field `AlgebraicClosure (ZMod p)` and smooth group `SL_N`.
The same reasoning would not justify arbitrary nonreduced group schemes or
evaluation only on the finite prime-field group. Neither substitution is
made here. This identifies an unformalized bridge, not a demonstrated
mathematical failure of the present model.

## BNP: the exact specialization

The original [BNP theorem](https://doi.org/10.1016/S0022-4049(01)00024-X)
was read in the existing local PDF and the historical page image
`RevisedWeb/investigation/root/bnp-transfer-page141.png`. Those two source
files were not included in the supplied archive.
Its ambient assumptions are a split, semisimple, simply connected algebraic
group over `F_p` and coefficients in its algebraic closure. In §7.5 set
`s=r=i=1`, `ν=0`, `u=b`, and `h=N`.
Then its conclusion specializes to

`H¹(SL_N(F_p), L(b·_p0)) ≅ H¹(SL_N, L(b·_p0))`.

Its bound is `p≥5(N−1)`; the base-weight inequality becomes `0<2(N−1)`.
The hypothesis that `u·ν` is `p`-restricted is precisely the hypothesis
present in the Lean interface. The theorem allows the extended affine group
generated by translations by `pX(T)`, so the balanced root-lattice affine
permutations are allowed. No additional winding class, Frobenius twist or
change from `F_p` to an unspecified extension remains in this specialization.

The theorem asserts an isomorphism; the current `Nonempty (… ≃ₗ[k] …)`
interface respects this. It does not assert that the isomorphism is the
particular cocycle restriction map defined elsewhere in the project.

## Highest weights, restriction and the simple quotient

[Steinberg 1963](https://doi.org/10.1017/S0027763000011016), §§2.7 and
4.7–4.9, constructs the restricted modules with each permitted highest
weight; §6.1 identifies rational simples by their highest weights.
Theorem 7.4 identifies distinct restricted highest weights with distinct
irreducible modules of the prime-field group. In particular a nonzero
restricted highest weight cannot restrict to the trivial module. The
[checked p.45](literature-audit/Steinberg1963-p45.png) states the allowed
simple-coroot labels as `0≤λ(a)≤q−1`, including the boundary value `p−1`.
Section 7.6 explicitly treats `SL_(l+1)(q)` and `PSL_(l+1)(q)`.

There is a useful distinction when reading [Steinberg's Yale notes](https://www.math.utah.edu/~ptrapa/math-library/steinberg/steinberg-yale-notes.pdf).
Section 4, [Theorem 5](literature-audit/Steinberg1967-Yale-s4-theorem5.png),
uses the adjoint **Chevalley group** defined in §3, generated by the root
subgroups. Section 3 identifies it as the image of the universal group with
kernel its center. For type A this is `SL_N(F_p)/Z`, hence PSL, not in general
`PGL_N(F_p)`. The current actual PSL definition has the correct meaning.
The rank and prime restrictions used in Lean avoid all listed exceptions.

The conversion from the code's `HasHighestWeight` and polynomial matrix
coefficients to this classification uses the regular-map comparison already
described. Quantifying over every `SimpleModule` is reasonable only with
that comparison and the uniqueness part of highest-weight classification;
the mere existence of a vector with a torus label would not suffice by itself.

## Andersen and the remaining precise task

The original article is
[Andersen, Advances in Mathematics 60 (1986), 125–153](https://doi.org/10.1016/S0001-8708(86)80008-1).
The publisher metadata was recovered and saved. The full-text endpoint
requires unavailable access; the PDF endpoints did not return a PDF.
The Aarhus catalogue exposed online preprints only from 1995 onwards;
an attempted older preprint path returned 404. These access results are not
evidence against the mathematical theorem.

The available [Lübeck formulation, Theorem 4.5](https://arxiv.org/html/1610.07055v2#S4.SS1),
has the source `V(y·0)` and target `L(x·0)`. Setting `y=e` gives `V(0)=k`,
not an arbitrary simple source. The formal interface uses only degree one;
it does not import the displayed all-degrees formula, whose printed `i>0`
omits the identity polynomial's degree-zero term when `x=y`.

For the exact convention comparison still to be certified directly from
Andersen, the required identity is

`dim H¹_rat(SL_N,L(b·_p0)) = [v]h_(w0,w0*b)(v)`.

Here `b` is finite-left-minimal, the induction is trivial/spherical, and
`h_(y,w)(v)=v^(ℓ(w)−ℓ(y)) P_(y,w)(v^−2)`. The family application uses
`b=u^−1`, so `w0*b=(u*w0)^−1`; simultaneous inversion then preserves the
ordinary fixed source `w0`. These indices are present literally in the code.
The unresolved task is to check the original Ext theorem's exact region and
its polynomial convention against this identity, including any enlargement
of the sufficiently-large-characteristic threshold needed for its region.
Replacing this task by an Ext formula with two varying simple sources would
not close it.

## What this audit changes

The AJS full-text access limitation is resolved. The already documented
rational-function/model comparison is now spelled out more precisely, and
the primary sources for BNP and Steinberg support the current scopes.
No transfer hypothesis was removed, no new one was introduced, and no
definite counterexample to the mathematical interfaces was found.

Further progress should separate the components of `AndersenAJS` for
auditability and formalize the polynomial/regular-map comparison. Until the
original Andersen convention check and those formal bridges are supplied,
the correct conclusion remains a Lean theorem conditional on the displayed
literature interfaces, not an unconditional machine-certified counterexample.


The later [Andersen follow-up](audit-andersen-followup.md) locates the
original 1986 targets at §2, especially Propositions 2.8 and 2.12, through
accessible original-author papers. Their quantum/category O analogues do
not close the modular fixed-source verification, and no new theorem from
them was inserted as a formalization assumption.
