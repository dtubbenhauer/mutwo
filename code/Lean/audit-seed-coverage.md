# Seed-example verification

Updated 2 November 2026 against `../main.tex`, Section “The first example
in pictures” (`sec:aggregate-calibration`). The previously documented
formalization coverage gap is closed by the declarations below. The
manuscript and its figures were not changed.

## What is now proved

`SeedPolynomials.diagonal_polynomial` identifies the actual ordinary affine
KL polynomial at the paper's fixed lower endpoint:

```
T.kl.polynomial w₀ (Family.upper (m:=2) (j:=2))
  = 1 + 4*X + 5*X^2 + 4*X^3 + 2*X^4.
```

`rank_one_polynomial` proves the corresponding smaller polynomial `1 + X`.
The two critical coefficients are therefore `1` and `2` (`rank_one_mu` and
`diagonal_mu`). Their only mathematical parameters are
`T : Hecke.Theory 5` and `W : PolynomialWebLiterature T`, the existing general
literature bundles. There is no assumed seed polynomial, decomposition,
family coefficient, or new literature input.

## Proof route and correspondence with the paper

1. **Actual affine indices.** `SeedCosets` constructs the five short
   spherical cosets as balanced periodic permutations, checks their
   windows, and proves minimality, length additivity and the identity
   `s₁ s₄ s₀ w₀ = C_{1;2}`. `SeedOneLineIndex` constructs the strong
   retained-line index with window `[7,5,4,3,-4]`, proves its packet matrix
   and finite descents, and identifies its actual integral morphism with
   its canonical basis element. Reflection reverses winding as well as
   residue order. The two retained-line indices have length 15; the source
   has length 10 and the two family indices have lengths 13 and 19.

2. **Rank-one correction.** `SeedRankOne.raw` is the actual algebra product
   `b₁ b₄ b₀ C_w₀`, where `bᵢ=Hᵢ+v`. `SeedRankOneCosets` proves the full
   finite-standard expansion of each spherical coset, rather than checking
   only the source coordinate. `corrected_diagonal`, `corrected_lower`
   and `corrected_bar` give the leading coefficient, strictly positive
   proper standard degrees and bar invariance. Canonical uniqueness then
   proves `canonical_identity`: `U₂−(v+v⁻¹)C_w₀=C_{1;2}`.
   `raw_inverse_convention` and `SeedRankOneConvention.canonical_inverse_identity`
   explicitly convert this to the paper's right-module word
   `Mₑ b₀ b₄ b₁`; the same fixed source is preserved.

3. **Exact five-term expansion (`lem:seed-expansion`).**
   `SeedDecompositionBounds` specializes the proved uniform support bounds:
   outside the origin all surviving multiplicities are constant, and the
   weak terms vanish. The actual gallery polynomial has constant
   coefficient one at each retained-line index. The source canonical
   element cannot reach those longer indices; proper KL coefficients
   have positive degree. Thus `strong_multiplicity` and
   `reflected_strong_multiplicity` prove that both multiplicities equal
   one. Together with the already proved family multiplicities and full
   spherical correction, `canonical_expansion` proves the exact vector
   identity. `web_expansion` writes its two auxiliary terms as the actual
   integral one-line morphisms.

4. **Four-web subtraction and source readout.**
   `SeedPolynomials.four_web_identity` proves the paper's equality
   `C_{2;2}=R₂−U₂−E₁,₂−E₁,₂ᵛ` in the actual Hecke algebra.
   `diagonal_source` proves its full normalized source coordinate
   `2v+4v³+5v⁵+4v⁷+v⁹` from that canonical expansion and the actual web
   coordinate formulas. The table below records all four evaluations.

5. **Actual KL identification (`eq:calibration-full-seed`).**
   `FamilyPolynomialReadout.of_source_coordinate` uses the proved family
   length gap and injectivity of `P ↦ vᴰP(v⁻²)`. At gap nine it identifies
   the actual KL polynomial with the displayed polynomial. The earlier
   `suppliedSeed_full` is used only to check the latter's Laurent reversal
   after the actual canonical coordinate has been proved.

## The four actual source coordinates

| Declaration | Coordinate at `w₀` |
|---|---|
| `SeedWebCoordinates.raw_source` | `v⁻¹ + 4v + 7v³ + 7v⁵ + 4v⁷ + v⁹` |
| `SeedRankOne.raw_source` | `v⁻¹ + 2v + v³` |
| `SeedWebCoordinates.one_line_source` | `v³ + v⁵` |
| `SeedWebCoordinates.reflected_one_line_source` | `v³ + v⁵` |

The previously checked corrected aggregate graph still has coordinate
`3v+7v³+7v⁵+4v⁷+v⁹`. It is distinct from the individual canonical coefficient
now proved above.

## Trust and scope

Finite window certificates are checked by Lean's kernel. No Python result,
`native_decide`, compiled oracle, new axiom or proof placeholder is used.
The standard mathematical literature inputs remain explicit theorem
parameters; this is not an unconditional construction of the entire KL
framework. The polynomial proof follows the manuscript's web calculation;
it is not an independent formalized KL-recursion implementation.

The seed proof is supplementary to the uniform row-sum/cohomology proof.
It is not inserted as an assumption into that proof, and it does not prove
the conjectural formula `mu_(j;m)=j` for arbitrary parameters.

## Verification

From this directory:

```sh
lake build Guralnick.SeedPolynomials Guralnick.SeedRankOneConvention
lake build
python3 scripts/verify.py
```

The audit target checks the principal declarations' foundational
axioms and contains explicitly typed applications of both seed polynomial
theorems, with only the established `T` and `W` inputs.
