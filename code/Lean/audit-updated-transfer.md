# Updated manuscript: cohomological transfer audit

2 November 2026. Target: `../main.tex`, especially
`rem:verification`, `lem:application-weight`,
`prop:application-transfer`, `lem:simple-quotient`, and
`cor:guralnick`. This records the comparison with the uploaded
`../Lean_verification_recommendations.pdf`, recommendation 1.
It does not modify the manuscript or add a mathematical assumption.

The updated application has the same weights, ordinary KL endpoints,
coefficient normalization, and characteristic bounds as the earlier
application in `../main_old.tex`. Its central-quotient argument is now the
separate `lem:simple-quotient`. The final Lean counterexample follows this
argument. The general cited theorems remain explicit hypotheses; no
source theorem has been formally proved merely by documenting it here.

## Exact external fields

The final representation-theoretic interface is
[`CoordinateLiteratureTransfer.Inputs`](Guralnick/CoordinateLiteratureTransfer.lean):

```lean
structure Inputs (T : Hecke.TheoryFamily) : Prop where
  existence : LiteratureTransfer.HighestWeightExistence
  andersen : AndersenAJS T
  bnp : BNP
  steinberg : LiteratureTransfer.Steinberg
  simple : LiteratureTransfer.PSLSimplicity
```

The following are the actual definitions of these five propositions, with
their existing namespace abbreviations retained. In the first, fourth and
fifth definitions the namespace is `Guralnick.LiteratureTransfer`; in the
second and third it is `Guralnick.CoordinateLiteratureTransfer`.

### `existence`: rational highest-weight modules

```lean
def HighestWeightExistence : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ wt : Weights.RootLattice (2 * m + 1),
      DominantRestricted (p : ℤ) wt.val →
      Nonempty (SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
```

`RootLattice n` is the actual integral sum-zero coordinate lattice.
`SimpleModule k n wt` contains a representation of `SL_n(k)`, its
finite-dimensional simple highest-weight property, and polynomial matrix
coefficients. It is not an object defined by its intended cohomology
dimension. The field quantifies over every dominant restricted
root-lattice weight, not only the paper's family.

Source: highest-weight classification, as used in Jantzen's
*Representations of Algebraic Groups*. The previously inspected primary
text is Steinberg (1963), §§2.7, 4.7–4.9 and 6.1. The formal
coordinate-representation and polynomial-function models are related by
proved constructions in
[`RationalCoordinateRepresentations.lean`](Guralnick/RationalCoordinateRepresentations.lean).
The classification/existence theorem itself is external.

### `andersen`: eventual fixed-source KL-to-cohomology formula

```lean
def AndersenAJS (T : Hecke.TheoryFamily) : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m), ∃ p₀ : ℕ,
    ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p → 2 * m + 1 < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (wt : Weights.RootLattice (2 * m + 1))
        (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
        (b : AffinePermutation (2 * m + 1)),
        finiteLeftMinimal (T m hm).coxeter b →
        DominantRestricted (p : ℤ) wt.val →
        wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
        letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
        (Module.finrank (Cohomology.PrimeClosure p) (CoordinateH1 A.polynomial) : ℤ) =
          ((T m hm).kl.standard.repr ((T m hm).kl.canonical
            (AffinePermutation.longest (2 * m + 1) * b))
            (AffinePermutation.longest (2 * m + 1))) 1
```

This is a composite literature input, not a verbatim theorem of AJS.
Its semantic content is

\[
\dim H^1_{\mathrm{rat}}(\mathrm{SL}_N,L(b\mathbin{\cdot_p}0))
=[v]m_{e,b}(v)=[v]h_{w_0,w_0b}(v),\qquad N=2m+1.
\]

Its components and source qualifications are as follows.

| Component | Source and hypotheses | Formal/source status |
|---|---|---|
| Eventual restricted character formula | AJS §§16.1 and 16.24, with the quantum/affine character results discussed in its introduction; Lübeck Theorem 3.1 | AJS and Lübeck were inspected. The threshold depends on the root system and applies uniformly to the relevant restricted region. No effective value is supplied. |
| Degree-one Weyl-to-simple Ext formula | Andersen (1986), §2; Lübeck Theorem 4.5, under the character formula, with dominant `x·0`, `y·0` and restricted `x·0` | Lübeck was inspected and explicitly specializes `y=e`, so the Weyl source is `V(0)=k`. The original Andersen full text has **not** been inspected. Accessible later papers of Andersen locate Propositions 2.8 and 2.12; they do not substitute a quantum or category-O theorem for the modular result. |
| Trivial-induced spherical/ordinary dictionary | Lübeck §2 and the manuscript's `sec:dictionary`; finite-parabolic canonical-basis framework of Williamson/Cui | The exact fixed-source ordinary formula is included in this interface. There is no separately constructed Lübeck induced-module object and comparison theorem on this transfer path. The project independently proves the family endpoint inversion and ordinary coefficient normalization. |
| Rational cohomology from regular cochains | Jantzen's **1985 Part I preprint**, §§4.14–4.16, Proposition 4.16 | The primary text was inspected. Its identification with derived rational cohomology is external. The coordinate tensor complex and polynomial-function cocycle complex are related by the proved `RationalCoordinate.h1Equiv`. Proposition numbering refers to that preprint, not automatically to the 2003 edition. |

The original Andersen convention check remains an outstanding
source-verification task. The exact formula used is supported by the
paper's expressly cited Lübeck formulation. This qualification is neither
a proved gap in the manuscript nor an unconditional verification of the
external input. See
[`audit-andersen-followup.md`](audit-andersen-followup.md) for the precise
remaining source task, and
[`audit-primary-transfer.md`](audit-primary-transfer.md) for checked pages.

Splitting this proposition into several renamed hypotheses would improve
navigation, but would not prove any connecting implication. In particular,
an arbitrary new predicate named `CharacterFormula` would not formalize the
character theorem. The present audit leaves the assumption unchanged.

### `bnp`: rational-to-finite prime-field comparison

```lean
def BNP : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime), 5 * (2 * m) ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (wt : Weights.RootLattice (2 * m + 1))
      (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt)
      (b : AffinePermutation (2 * m + 1)),
      DominantRestricted (p : ℤ) wt.val →
      wt.val = b.dotZero (p : ℤ) (Weights.rho m) →
      letI : FiniteDimensional (Cohomology.PrimeClosure p) A.rep := A.highest.1
      Nonempty (CoordinateH1 A.polynomial ≃ₗ[Cohomology.PrimeClosure p]
        Cohomology.H1 (restrictPrime (2 * m + 1) p A.rep))
```

Source: Bendel–Nakano–Pillen §7.5/Theorem 7.5; Lübeck Theorem 4.6.
The primary theorem was inspected. Set the cohomological bound `s=1`,
field exponent `r=1`, base weight `ν=0`, and affine element `u=b`.
The Coxeter number is `h=N`, hence `5(h-1)=5(2m)`. The split simply
connected group is `SL_N` over `F_p`, with coefficient field its
algebraic closure. The input uses the restricted principal-block condition
literally. Balanced root-lattice affine permutations are contained in the
extended affine group allowed by the source theorem.

Only the existence of a linear isomorphism is assumed. The project does
not additionally assume or claim that it equals a particular previously
defined cocycle restriction map. The prime-field exponent stays `r=1`;
there is no replacement by an unspecified sufficiently large finite
extension field.

### `steinberg`: restricted irreducibility

```lean
def Steinberg : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (wt : Weights.RootLattice (2 * m + 1))
      (A : SimpleModule (Cohomology.PrimeClosure p) (2 * m + 1) wt),
      DominantRestricted (p : ℤ) wt.val →
      Cohomology.Irreducible (restrictPrime (2 * m + 1) p A.rep)
```

Source: Steinberg (1963), §§6.1 and 7.4; the paper also cites §§1.3 and
Lübeck Proposition 5.3. The primary text was inspected, including the
restricted range `0 ≤ <λ,αᵢ∨> ≤ p-1`. The field supplies irreducibility
only. The family's nontriviality is proved directly from its highest-weight
vector and a finite diagonal element in
`HighestWeight.family_restrictPrime_nontrivial`.

### `simple`: simplicity of the actual PSL quotient

```lean
def PSLSimplicity : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (p : ℕ) (hp : p.Prime), 5 * (2 * m) ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    IsSimpleGroup (Cohomology.PSL m p)
```

Source: Steinberg's Yale notes, §4, Theorem 5, with the central-quotient
description in §3. These passages were inspected. The group is
`SL_N(F_p)/Z`, not all rational points of the adjoint algebraic group
`PGL_N`. Here `N≥5`, so the small simplicity exceptions are avoided.
The stated `5(2m)` bound is stronger than necessary for this field but is
already needed for BNP; no extra restriction on the final examples is
introduced.

## The convention conversion used by the family

The following are proved parts of the project, rather than additional
fields of the five-input bundle.

1. The manuscript's increasing affine window is `Family.affine hm hj hjm`.
   `Family.upper` is its product with the finite longest element on the
   right. The family and its matrix and length data are defined before
   choosing KL or representation-theoretic inputs.
2. `Weights.familyWeight m j p` is the displayed sum-zero coordinate
   vector. `FidelityWeights.coordinate_eq_manuscript` and
   `FidelityWeights.dynkin_eq_manuscript` identify it with
   `(c+2)η_(j-1)+(p-c-3)η_j+η_m`, including overlapping terms when `j=m`.
3. `LiteratureTransfer.family_dot_label` proves
   `familyWeight.val = (Family.affine ...)⁻¹.dotZero p (Weights.rho m)`.
   The integer `p` multiplies the translation coordinates in the positive
   dot action. `Weights.rho m i=m-i` is the zero-based version of the
   paper's `(N+1-2i)/2`.
4. The increasing window gives no finite **right** descents. Inversion
   therefore gives no finite **left** descents for `b=u⁻¹`, by
   `Hecke.inverse_family_no_finite_left_descent`. This matches Lübeck's
   representatives of `W_J \ W`, regardless of the words “right coset
   representatives” in his notation paragraph.
5. The ordinary endpoint is literally `w₀*b=(u*w₀)⁻¹`.
   `Family.upper_inverse` proves this identity. The lower endpoint stays
   `w₀`, since `w₀⁻¹=w₀`. `Hecke.Theory.inversion` proves KL inversion
   invariance from the KL realization, and
   `Hecke.coefficients_inverse_canonical` supplies the exact equality
   used in the family transfer.
6. The Hecke relation is `(H_s-v⁻¹)(H_s+v)=0`, with
   `C_s=H_s+v`; lower canonical coefficients lie in `v Z[v]`.
   Ordinary polynomials use `Q=v⁻²`:
   `h_(y,w)=v^(ℓ(w)-ℓ(y)) P_(y,w)(v⁻²)`.
   `Hecke.familyMu_canonical` proves that the coefficient of `v` is
   the paper's coefficient of `Q^((D_(j;m)-1)/2)`. Trivial induction is
   spherical. No sign-induced/antispherical coefficient occurs.
7. The module is chosen by its highest weight through
   `LiteratureTransfer.familyAlgebraic`; `familyModule` then restricts
   to `SL_N(F_p)` and descends to the central quotient.
   `familyModule_h1_dimension` connects its actual first cohomology to
   the ordinary fixed-source coefficient. It does not use a row sum.
8. Root-lattice central triviality, invertibility of the finite center's
   order, and the `H¹` equivalence on descent are proved in
   [`SLQuotient.lean`](Guralnick/SLQuotient.lean) and its imports.
   Irreducibility and the directly proved nontriviality, together with
   the simplicity input, give faithfulness. Absolute irreducibility
   over the algebraic closure is proved using actual scalar extension.

The coordinate-to-function comparison is also proved, not assumed:
`CoordinateLiteratureTransfer.andersen_iff_function` and
`bnp_iff_function` prove equivalence with the older transfer interfaces,
using `RationalCoordinate.h1Equiv`. Its interpretation as derived rational
cohomology remains the cited Jantzen theorem described above.

## Characteristic scope: a precise limit of the current formulation

The manuscript's `prop:application-transfer` is stated for any chosen
prime satisfying the BNP bound **and** validity of Lusztig's restricted
character formula. The current Lean interface instead bundles AJS with
Andersen and supplies an eventual threshold `p₀(m)`, proving transfer
for every prime beyond that threshold, with `p>N` and the separate
BNP bound `p≥5(N-1)`.

This proves the exact eventual-prime quantifiers in `cor:guralnick`.
It does **not** separately formalize the more flexible proposition for
every prime where someone independently knows the character formula,
possibly below the selected threshold. There is currently no standalone
character-formula predicate with its character/multiplicity objects and
an Andersen implication from that predicate. This is an explicitly
unformalized formulation of an intermediate literature-based proposition,
not a change to the counterexample's final quantifiers.

The AJS threshold and BNP bound have different roles. `p≥5(N-1)` alone
is never asserted to prove the character formula. Neither threshold
asserts unboundedness in a fixed characteristic as the rank increases.

## Endpoint and hidden-hypothesis check

The final declaration is literally:

```lean
theorem not_absoluteBoundedness (T : Hecke.TheoryFamily)
    (W : ∀ m hm, PolynomialWebLiterature (T m hm))
    (I : CoordinateLiteratureTransfer.Inputs T) :
    ¬Cohomology.AbsoluteBoundedness
```

Its namespace is `Guralnick.ModelComparisonCounterexample`.
`AbsoluteBoundedness` means that one natural bound works for every field,
finite group, and faithful finite-dimensional absolutely irreducible
representation, with `H1` equal to mathlib's `groupCohomology A 1`.
`Cohomology.h1IsoExtFromTrivial` identifies the source as the actual
trivial representation. It is not an arbitrary-pair extension bound.

Inspection of these source declarations found no extra family coefficient,
row sum, graph evaluation, or transfer equality as a hidden final argument.
The `Fact p.Prime` and finite-dimensional instances in the field statements
are constructed from the displayed prime hypothesis and the actual
highest-weight module's properties. They are not unspecified additional
mathematical inputs. The positivity, Coxeter, KL, refinement, and
full-flag hypotheses inside `T` and `W` remain as recorded in
[`literature-inputs.md`](literature-inputs.md).

This source inspection does not establish that those literature structures
exist, and an axiom-dependency check cannot establish their correspondence
with source theorems. Both the typed endpoint checks and this semantic
comparison are needed. The manuscript's phrase “as axioms” should be
understood mathematically: the implementation uses explicit assumptions,
not newly declared Lean `axiom`s.

## Relation to the verification remark

The updated `rem:verification` accurately distinguishes the proved
family calculation and fixed-graph evaluation from background inputs.
Its claim about the first-cohomology deduction is conditional in exactly
the way documented here. Two details should remain visible in release
documentation:

- The original Andersen theorem has not been independently inspected;
  Lübeck is the checked exposition that the manuscript also cites.
- The general spherical/ordinary identification is included in the
  transfer input, even though the family-specific inversion and
  coefficient/weight conversions are separately proved.

The remark lists KL positivity among the assumptions and cites geometric
sources. The actual `Hecke.PositivityInput` comments and literature ledger
point specifically to Elias–Williamson, Corollary 1.2(1),(2). That paper is
present in the updated bibliography as `EliasWilliamson`, but is not in
the remark's citation list. This is a citation-ledger alignment detail,
not an added input or a mathematical gap; the manuscript was left unchanged.

The paper does not prove the background literature theorems, and faithful
formalization does not require re-proving them. The meaningful standard is
that the assumed statements have the cited meaning and that all
family-specific deductions between them are proved. The current audit
found no changed cohomological claim requiring a replacement of the
existing mathematical interfaces.
