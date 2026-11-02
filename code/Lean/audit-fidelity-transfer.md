# Adversarial fidelity audit: groups, modules and cohomology transfer

Date: 30 October 2026. Scope: the application section of the unchanged
`../main.tex`, lines 5487–5668, and the actual definitions used by
`WebProof.named_row_and_lower_bound` and `not_absoluteBoundedness`.
This is a semantic inspection of the definitions and literature interfaces,
not an inference from `lake build` or a repetition of the previous audit.

## Findings

No definite mathematical mismatch was found in this part of the formalization.
The witnesses are the intended PSL groups and highest-weight modules, the
source is the trivial module, and the dimension is actual first cohomology.
This conclusion is limited to the transfer interfaces inspected here: it
is not a consistency proof for all external assumptions in `WebLiterature`.

Two concrete improvements were identified:

1. The actual module weight was defined by the manuscript's displayed
   sum-zero coordinates, while the primary definition in the manuscript is
   a fundamental-weight combination. Existing code established dominance,
   restrictedness, regularity and the affine dot label, but did not contain
   an explicit equality of its Dynkin labels with that primary combination.
   `Guralnick/FidelityWeights.lean` supplies an independent uniform comparison,
   including `j=1`, the overlap `j=m`, and both displayed `m=2` examples.
   It also defines the integral vector `eta_r` with `+1` on its first `r`
   entries and `-1` on its last `r` entries, proves its sum is zero, and
   identifies it with the standard rational-coordinate formula for
   `omega_r + omega_(N-r)`. `coordinate_eq_manuscript` then identifies the
   actual module weight with the primary formula as a whole vector,
   independently of the Dynkin-label comparison. This strengthens the
   identity check; no incorrect weight was found.
2. The introductory comment of `Guralnick/Cohomology.lean` (lines 6–29 in
   the audited snapshot) describes the initial partial development. It says
   that named modules, the scalar-extension criterion and the row theorem
   are unformalized, although later modules now supply them. This is stale
   documentation, not a defect in the declarations. It should explicitly
   describe this file as a generic intermediate implication and point to
   `LiteratureTransfer`, `AbsoluteIrreducibility` and `WebProof`. These
   introductory comments were corrected during this audit; declarations
   and hypotheses were unchanged.

## Statement and quantifiers

`AbsoluteUniformH1Bound` in `AbsoluteIrreducibility.lean:88` quantifies over
all fields, all finite groups, and finite-dimensional faithful absolutely
irreducible representations. `H1` in `Cohomology.lean:41` is mathlib's
`groupCohomology A 1`, and `h1Dimension` takes its finrank. The final witnesses
have finite-dimensional H1 by `FiniteCohomology.finiteDimensional_H1`;
there is no use of the default zero finrank of an infinite-dimensional space.

The manuscript's exact formulation agrees with Lübeck's Conjecture 4.4.
His Theorems 3.1, 4.5 and 4.6 also confirm the separate rank-dependent
character-formula threshold, degree-one trivial-source interpretation and
finite-group comparison used here. The formalization does not claim a
bound on the AJS threshold from the BNP inequality alone, or unboundedness
in a single fixed characteristic. [Lübeck](https://arxiv.org/html/1610.07055v2)

`WebProof.named_row_and_lower_bound` fixes each `m>=2` and every prime
satisfying the actual rank threshold, `p>N`, and `p>=5(N-1)`. Its module
family has one member for each `j=1,...,m`; it proves the doubled row sum
and lower bound `floor(m/2)+1`. These are the manuscript's row sum and
ceiling bound. The final contradiction chooses arbitrarily large primes;
it does not quietly replace “every sufficiently large prime” by a single
small computational example.

## The groups and modules are the intended objects

- `Cohomology.PSL m p` is mathlib's projective special linear group over
  `ZMod p`, of matrix size `2*m+1`, rather than a type carrying the name PSL.
- `SimpleModule` (`LiteratureTransfer.lean:29`) contains an actual
  representation of `SL_N(AlgebraicClosure (ZMod p))`, finite dimension,
  irreducibility, polynomial action, and a nonzero highest-weight vector.
- `HasHighestWeight` (`HighestWeight.lean:35`) specifies upper-unipotent
  invariance and the character `product t_i^(weight_i)` of the actual
  diagonal determinant-one torus. Upper triangular unipotents agree with
  the dominant convention of nonnegative adjacent weight differences.
- `familyAlgebraic` (`LiteratureTransfer.lean:110`) selects a module by this
  actual weight property. Its choice is not indexed by a desired cohomology
  dimension. General highest-weight classification/uniqueness remains
  external; the transfer assumptions quantify over every module satisfying
  these independently defined properties.
- `restrictPrime` is restriction along entrywise inclusion of prime-field
  matrices. `SLQuotient.descended` (`SLQuotient.lean:79`) is the actual
  quotient representation by the finite SL center.

The weight vector is not defined from KL data. Its dot-action equality is
proved for the inverse affine window. The root-lattice condition is an
integer sum-zero condition, not a congruence modulo characteristic. On the
algebraically closed coefficient field, integer torus characters are the
usual algebraic characters, so this does not conflate distinct restricted
weights through evaluation only on prime-field points.

## Rational cohomology is not abstract algebraic-group cohomology

`RationalCohomology.regularMaps` is the range of evaluation of actual finite
vector-valued polynomials in SL matrix entries. The code proves equivalence
with polynomial matrix coefficients in a finite basis. `RationalH1`
(`RationalCohomology.lean:215`) is regular crossed homomorphisms modulo the
actual coboundaries. Every coboundary of a polynomial representation is
proved regular, and `rationalBoundaries_eq_range` identifies the denominator
with the entire coboundary image.

The map to unrestricted abstract-group H1 is proved injective, not declared
an isomorphism. The literature inputs are applied only over an algebraic
closure of a prime field. On other fields, the function-space predicates
alone would not identify scheme-theoretic rational representations; the
source file explicitly warns about that distinction.

The comparison of regular cochains with derived rational algebraic-group
cohomology remains external. Jantzen's 1985 preprint §§4.14–4.16,
Proposition 4.16, is the relevant general comparison. It is bundled in the
stated `AndersenAJS` input, not proved by the finite-group Ext theorem.
[Jantzen](https://archive.mpim-bonn.mpg.de/id/eprint/607/1/preprint_1985_9.pdf)

## Fixed-source transfer and the external hypotheses

`AndersenAJS` (`LiteratureTransfer.lean:53`) ranges over all restricted
principal-block dominant weights in each rank and all corresponding simple
polynomial modules. Its upper index is literally `w0*b` and its lower index
is literally `w0`. The specialization uses `b=u^(-1)`, proved finite-left
minimal. Simultaneous inversion identifies its ordinary coefficient with
that of `C=u*w0`. No arbitrary lower endpoint or arbitrary pair of simple
Ext sources enters this application.

This interface combines several general statements rather than quoting a
single theorem verbatim. Original Andersen and AJS proofs remain external;
the source checking here independently reread Lübeck's precise formulation.
The formal statement is not a family-specific cohomology identity, but its
correct normalization and model interpretation still require this external
mathematical comparison.

The original BNP theorem was checked in the local journal page image
`RevisedWeb/investigation/root/bnp-transfer-page141.png`, p.141, §7.5.
It permits `s>=1`, `p>=(4s+1)(h-1)`, restricted base weight nu below the
stated highest-coroot bound, and a translated p^r-restricted target.
Substituting `s=r=1`, `nu=0`, `h=N` gives exactly the Lean `BNP` input.
The actual root-lattice affine group is contained in the extended affine
group allowed by the theorem. The interface asks only for an isomorphism;
it does not assert that a particular cocycle restriction map is that
isomorphism. The publisher page was inaccessible in this check; the original
local page image and text were available.
[BNP](https://doi.org/10.1016/S0022-4049(01)00024-X)

## Central descent, faithfulness and absolute irreducibility

These conclusions are not silently bundled into the KL equality:

- Root-lattice torus character gives trivial scalar-center action, and
  irreducibility propagates fixation of the highest-weight vector to the
  whole module (`HighestWeight.root_lattice_center_trivial`).
- The finite center embeds in the unit group of `ZMod p`; its order is
  positive and less than p, hence invertible in the coefficient field
  (`SLQuotient.center_order_invertible`). The weaker bound used in Lean
  suffices for the manuscript's argument, without needing the exact gcd.
- Central inflation is an actual linear equivalence. The distinction
  between the quotient acting on invariants and the quotient acting on the
  whole module is bridged explicitly in `CentralQuotient`.
- General Steinberg restriction and PSL simplicity remain stated literature
  hypotheses. Nontriviality plus simplicity proves faithfulness internally.
- Absolute irreducibility means irreducibility of the actual tensor-product
  representation over an algebraic closure (`AbsoluteIrreducibility.lean:29`).
  Over the already algebraically closed coefficient field, the scalar map
  is an isomorphism and the required property is proved, not assumed.

No new mathematical axiom, change to the manuscript or weakening of the
counterexample statement was needed by this transfer audit. The added
weight comparison is an independent fidelity check, not a substitute for
formalizing Andersen, AJS, BNP or highest-weight classification themselves.

## Verification of the added checks

`lake build Guralnick.FidelityWeights` succeeds. The principal declarations
are `dynkin_eq_manuscript`, `coordinate_eq_manuscript`,
`etaCoordinate_eq_fundamental`, `etaCoordinate_sum`, `m2_j1_labels` and
`m2_j2_labels`, all in `Guralnick.FidelityWeights`. None takes a literature
interface, cohomological identity, or KL equality as a hypothesis.
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`
for each of these six declarations; no additional mathematical axiom or
compiled decision procedure is involved.
