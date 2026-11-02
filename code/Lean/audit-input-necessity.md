# Which literature inputs the proof actually needs

30 October 2026. This audit distinguishes the proved web row identity from
its cohomological application, and distinguishes a sufficient input from a
logically independent or minimal one. The earlier list of eleven packages
was an inventory of interfaces, not a claim that eleven independent
external results were indispensable.

## Concrete changes from the necessity audit

1. **The separate Schur-support premise is redundant.**
   `CanonicalRefinement.StandardCompatibility` places each canonical
   double-coset maximum in the span of actual normalized double-coset sums.
   `SchurCornerEigen` proves those sums satisfy the spherical eigenconditions.
   `HeckeEigenCoordinates.eigen_top_doubleMaximal` proves that the maximal
   length in any canonical expansion of an eigenvector has the required
   descents. Subtracting that canonical term and inducting on finite support
   gives `CanonicalSchurFromRefinement.toCompatibility`. This derivation
   uses neither positivity nor convolution. The `schur_product` field is
   removed from the final bundle; `refinement` remains.
2. **Bar involutivity is redundant as a separate KL field.** The canonical
   basis is fixed by bar, and Laurent scalar inversion squares to the
   identity. Expanding a vector in that basis proves involutivity in
   `KLDerivedBar.bar_involutive`. The old field is removed.
3. **Steinberg nontriviality is unnecessary for this family.**
   `HighestWeight.family_restrictPrime_nontrivial` constructs a prime-field
   diagonal element with two minus signs whose action on the actual
   highest-weight vector is minus one. The Steinberg input now supplies
   only restricted irreducibility.
4. **Andersen's separate H¹ finiteness conjunct is unnecessary here.**
   The application used only the dimension equality. Finite-dimensionality
   of the actual finite-group cohomology is proved independently; BNP can
   transport it to the rational/coordinate model when needed. Both Andersen
   interfaces now assume only the dimension equality. They are equivalent
   to each other by the proved cochain-model comparison. This does not claim
   that the weaker equality-only statement alone implies the old finiteness
   clause outside BNP's characteristic range.

These changes preserve the original ordinary lower endpoint w₀, the named
highest-weight modules, the row identity, and the faithful absolutely
irreducible counterexamples. They remove assumptions rather than replacing
those conclusions by a weaker target.

## Dependency by conclusion

The numbering below refers to the earlier eleven-item list.

| Earlier input | Web row-sum theorem | Named faithful PSL counterexamples | Actual role and scope |
|---|---|---|---|
| 1. Affine Coxeter realization | Used | Inherited | Identifies actual windows, lengths and descents; only odd ambient degrees N≥5 are needed. |
| 2. Ordinary KL realization | Used | Inherited | Defines the actual standard/canonical bases and ordinary polynomials. Involutivity is now derived. |
| 3. Positivity | Both parts used | Inherited | Ordinary coefficient positivity prevents cancellation in support/degree bounds. Product positivity controls the cleared parabolic numerators. |
| 4. Schur product support | **Derived from 5** | **Derived from 5** | No longer an independent final input. |
| 5. Canonical Schur standard span | Used | Inherited | Supplies canonical corner support and spherical-to-family coefficient ratios. |
| 6. Full-flag orbit/Hecke realization | Used | Inherited | Connects the actual Hecke products with the actual flag configurations being counted. |
| 7. Highest-weight module existence | Not used | Used | Constructs actual modules; universal statements about all simple modules do not supply their existence. |
| 8. Andersen/AJS transfer | Not used | Used | Identifies the fixed-source ordinary coefficient with rational/coordinate H¹ at a suitable characteristic. |
| 9. BNP comparison | Not used | Used | Transfers that dimension to the prime-field finite group. |
| 10. Steinberg restriction | Not used | Irreducibility used | Nontriviality is now proved from the family's explicit torus character. |
| 11. PSL simplicity | Not used | Used for faithfulness | Nontrivial action on a simple group has trivial kernel. It is not used in the H¹ calculation. |

Thus the final interface has ten named packages: three Hecke packages, two
web packages, and five representation packages. This count is bookkeeping,
not a claim of logical independence or of a minimal possible bibliography.

## Where the general statements exceed this application

**Positivity.** Full positivity for products of arbitrary canonical elements
is stronger than the consumers require. The numerator argument only needs
successive products by canonical longest elements of finite parabolics
(the actual three/four-factor products in `CanonicalChains` and
`ParabolicWeb`). Standard coefficient positivity is a separate active
ingredient. The current general positivity interface remains convenient;
this audit does not remove its theorem or claim the two kinds of positivity
follow from one another. Elias–Williamson supplies both in one reference.

**Schur compatibility.** The original direct use of refinement was the
full-spherical-to-family ratio in `MainContributionSupport`; the one-line
ratio lemma is not on the final proof path. After the reduction above,
refinement also supplies canonical support for all corners used by the
construction. Keeping its general finitary statement avoids hiding the
family's canonicality in a custom premise.

**Convolution.** Binary full-flag convolution is genuinely used in this
proof architecture. Its partial-gallery formula, full-lift counts, and
normalization are internal deductions. A direct Hecke multiplication proof
could replace the external realization, but that would be another proof,
not deletion of an unused field. The whole annular web presentation and
global annular isotopy invariance are not assumptions of this fixed-graph
six-map proof.

**Characteristic and weight scope.** The named row theorem needs only the
m displayed weights at each rank, at a common sufficiently large prime.
Eventual bounds for those finitely many indices can be combined by taking
a maximum. The current all-restricted-label/all-simple-module interfaces
are stronger than this use, and express the standard general theorems.
For the bare negation of absolute boundedness, even less suffices: an
unbounded sequence of ranks and, at each rank, one large-coefficient member
and one suitable prime. The current contradiction uses ranks m=2C+2.
These observations do not justify a fixed-characteristic claim, removal of
the characteristic bounds, or omission of the trivial-source condition.

**Faithfulness.** PSL simplicity could be replaced by a direct proof that
the selected module is faithful. It cannot simply be omitted: faithful
modules are part of `AbsoluteBoundedness`. Quotienting an arbitrary action
by its kernel does not automatically preserve a lower bound on H¹;
inflation goes from the quotient's cohomology into the original group's.
Existence and restricted irreducibility can be cited together from
Steinberg, but grouping them does not eliminate either mathematical role.

**Jantzen's cohomological interpretation.** This is a shared bridge inside
the Andersen and BNP source formulations, not a sixth representation field
or two independent assumptions. The project's coordinate/function
comparison is proved; identifying the regular complex with derived rational
cohomology remains external. Citing a composed finite-group KL/H¹ theorem
could bundle these steps, but would not constitute a Lean proof of them.

## References actually supporting this route

- Björner–Brenti, *Affine Permutations of Type A*, §3: affine window model.
- Kazhdan–Lusztig (1979): ordinary Hecke/KL realization.
- Elias–Williamson, Corollary 1.2(1),(2): the two positivity uses.
- Williamson, *Singular Soergel bimodules*, corrected version, §2.3:
  canonical/standard Schur span. Cui §3 provides its affine Schur formulation.
  There is no longer a second independent Schur-support input.
- Lusztig, *Aperiodicity in quantum affine gl_n*, §§1.3–1.9, and Cui §7.1,
  Lemma 7.1: full-flag orbit classification and binary Hecke convolution.
- Steinberg (1963): highest-weight existence and restricted irreducibility.
- AJS, Andersen, and Jantzen's regular cochain theorem, in the fixed-source
  conventions explained by Lübeck: rational KL-to-H¹ transfer.
- Bendel–Nakano–Pillen, Theorem 7.5: prime-field cohomology comparison.
- Steinberg's Yale notes, §4, Theorem 5: PSL simplicity for faithfulness.

Scott–Xi, the earlier finite-type paper, and the broader annular-web papers
of Queffelec, Lacabanne–Tubbenhauer–Vaz, and Cautis–Kamnitzer are not additional
premises of the final Lean theorem. They can remain important citations for
history, interpretation, and motivation. Likewise SSW explains the web
presentation, while this formal proof constructs and evaluates the specific
six-map graph directly. Du–Fu's general multiplication formulas and Cui's
matrix-dimension theorem are not assumed: the required dimension dictionary
is proved from inversions. A paper may therefore deserve citation without
being a theorem assumed by this formalization.

The exact links and source-verification qualifications are maintained in
`literature-inputs.md`. In particular Andersen's original 1986 theorem has
not been independently checked in full text; the present convention check
uses Lübeck. This audit does not upgrade that qualification.

## Evidence and its limits

The source audit records actual consumers rather than merely imports.
`reports/proof-value-dependencies.lean` traverses elaborated project proof
values and records projection uses and paths; the original scan is saved
as `reports/proof-value-dependencies-baseline.json`. Types and imported
modules alone do not show that a field is used. Even a value-closure scan
can overcount when a whole structure is passed or copied, so the concrete
consumer lemmas and the proved reductions above supply the stronger
conclusions. This is an audit aid, not a proof of logical minimality.

The final rescan is saved as `reports/proof-value-dependencies.json`, and
`reports/proof-value-dependency-comparison.json` compares it with the preserved
baseline. Both the old `schur_product` projection and its product-support
projection disappear from all three final theorem value closures. Refinement
now has two concrete consumers: canonical corner membership and the coordinate
ratio theorem. The row theorem reaches none of the five cohomological inputs;
the named-family theorem and negation of boundedness reach all five.
The scanner does not measure changes inside field types, so the Andersen
and Steinberg weakenings are justified by the edited definitions and their
checked consumers, not by projection counts.

To reproduce this supplementary audit after `lake build`:

```sh
lake env lean reports/proof-value-dependencies.lean
python3 reports/compare-proof-dependencies.py
```

The integrated build, principal axiom checks, original certificate
regeneration and unchanged-manuscript hash are recorded in
`reports/verification.json`. No new mathematical axiom or numerical
replacement for the actual objects is introduced by this reduction.

Final integrated verification passed: 237 project Lean sources, 270 principal
axiom checks, only `propext`, `Classical.choice`, and `Quot.sound`. Certificate
regeneration was identical and the manuscript hash unchanged. The final
counterexample remains conditional on the explicitly retained inputs.
