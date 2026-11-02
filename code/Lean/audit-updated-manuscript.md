# Comparison with the updated manuscript

Reviewed 2 November 2026. The targets are `../main.tex` and
`../Lean_verification_recommendations.pdf`. Their exact hashes are recorded
in `certificates/manuscript-review.json`. The earlier manuscript is now
`../main_old.tex`; its hash agrees with the original source inventory.
Neither manuscript nor the recommendations was edited.

## Scope and outcome

The updated mathematical text, definitions, proofs, examples and
bibliography have been read, together with the recommendations. The main
web's TikZ incidence and seam conventions were compared with `Web.family`.
The comparison is a mathematical/source audit, not a Lean proof that a TeX
file expresses a theorem.

The explicit shifts, sorted affine windows, period-three matrices, six
parabolic maps, four-case gallery count, six surviving families, auxiliary
canonicality, correction and row sum have the same mathematical content as
the previous manuscript. The notation is now consistently `A_{j;m}` and
`D_{j;m}`; Lean's argument order remains `(m,j)`. This changes notation,
not the family. The final theorem is still the row-sum theorem, not the
conjectural individual rule `mu_{j;m}=j`.

No new mathematical gap in this core argument was established by the
comparison. This does not certify every assertion in the manuscript or
discharge the cited literature. In particular, the following distinctions
matter for the meaning of “verifies the arguments of this paper.”

| Manuscript content | Present formalization boundary |
|---|---|
| `thm:intro`, `thm:aggregate-web` | Actual ordinary affine KL row with lower endpoint `w0`, proved from the documented general Hecke, refinement and full-flag inputs. |
| `cor:intro-guralnick`, `cor:guralnick` | The same named PSL modules and every sufficiently large prime, conditional on the documented representation-theoretic inputs. |
| `prop:application-transfer` | The eventual-characteristic version is proved. The paper also phrases the proposition for a prime at which the character formula holds; Lean does not separately define that predicate and prove this finer conditional version. See `audit-updated-transfer.md`. |
| `lem:seed-expansion` and §7's rank-one subtraction | Now proved in `SeedDecomposition.web_expansion` and `SeedRankOne.canonical_identity`, including both retained-line multiplicities one and full rank-one triangularity. |
| `eq:calibration-full-seed` | Now proved as the actual ordinary fixed-source KL polynomial in `SeedPolynomials.diagonal_polynomial`, from the canonical vector identities and normalization injectivity. |
| §9's individual rows for `m=3,4,5` | Experimental comparison data. The row totals follow from the theorem; the individual entries have no kernel-checked KL certificates here. |
| §9's question `mu_{j;m}=j` for all parameters | Open in the paper and not claimed or assumed in Lean. |
| `lem:web-realization`, `lem:annular-relations`, `lem:boundary-rotation` | The global annular category, isotopy quotient, all coil/braid relations and categorical equivalence are cited background, not formalized. The fixed graph-to-six-map equality is proved and suffices for the algebraic calculation. |
| New toroidal closure/Heawood discussion | Illustrative graph topology, not part of the counterexample proof and not formalized. The existing graph has 12 internal vertices and 20 open edges; it is not the closed 14-vertex, 21-edge graph. |

`SeedWebCoordinates.lean` now proves the actual six-map source coefficient,
both one-line source coefficients, and the corrected graph's aggregate
coefficient. These specialize the proved gallery theorems with only the
existing general inputs. `SeedRankOne.raw_source` now supplies the fourth
row, and `SeedPolynomials` completes the canonical assembly and actual KL
identification. See `audit-seed-coverage.md` for the complete proof route.

The verification remark's phrase “as axioms” means explicit mathematical
hypotheses. The source declares no new Lean axioms. Its final theorem has
arguments `T`, `W` and `I`, whose existence is not proved. A successful
foundational axiom audit does not prove that those inputs accurately state
the literature; the source/convention ledgers address that separate task.

## Decisions on the five recommendations

1. Retain the genuine cited inputs. Make their fields and convention
   conversions individually inspectable in `literature-inputs.md`,
   `audit-framework-inputs.md` and `audit-updated-transfer.md`.
   Splitting `AndersenAJS` into names without defining the intervening
   character/Ext statements would not add a proof. Original Andersen
   full-text verification remains qualified; Lübeck is the checked route
   used by the paper.
2. Replace passive-only endpoint checking with failing Lean guards and
   explicitly typed applications. Keep the general literature parameters,
   fixed source, named module family and all characteristic bounds visible.
3. Prioritize an actual seed KL identification over further arithmetic
   checks of a supplied polynomial. A faithful route can follow §7 rather
   than introduce an independent general KL implementation: prove the
   rank-one word's canonical correction and the two seed one-line
   multiplicities, then use the already proved web coefficient formulas.
   This route is now implemented through `SeedPolynomials.diagonal_polynomial`;
   no seed identity was inserted as an input.
4. Retain `CanonicalRefinement.StandardCompatibility` as the paper's cited
   general Schur input. Deriving it from Coxeter/KL theory would strengthen
   the library, but is not necessary for faithfulness to a paper which
   invokes that literature. `HeckeEigenCoordinates` proves constraints on
   an already known eigenvector; it does not by itself prove that every
   canonical element with descents is that eigenvector. Avoid a circular
   use of the retained refinement assumption in an attempted removal.
5. Build a mathematical-library target and a separate audit target, both
   required by the default build and portable release command. Preserve
   pins, current manuscript provenance, exact statement map and source
   hashes. Local release checks do not imply that hosted CI or repository
   branch protection has been configured.

## Seed follow-up completed

The seed identification was original mathematics worked out in the paper,
so closing it took priority over reproving the general Schur refinement
theorem or global web-category equivalence. It now establishes equality
with `KLRealization.polynomial` through actual canonical Hecke elements.
This strengthens coverage without enlarging the literature assumptions.

The individual conjecture, stronger growth, fixed-characteristic
unboundedness and global isotopy theory are not additional obligations of
this verification of the main result.
