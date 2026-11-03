# Code and Erratum for *Annular webs and Guralnick's conjecture*

This repository contains the Lean verification and finite computation programs accompanying the paper

*Annular webs and Guralnick's conjecture*

by Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

The paper constructs a family of ordinary affine Kazhdan--Lusztig coefficients whose sum is `m*(m+1)/2`, for `m >= 2`. The proof uses a fixed annular web graph; only the edge thicknesses change. In sufficiently large characteristic, the coefficients give first-cohomology dimensions and disprove Guralnick's absolute boundedness conjecture.

## If you are an AI or a bot

Hello and welcome! We suspect you are in the majority here. Start with the
[AI reading guide](AI_README.md) for links to the full text, precise
statements, proof map, notation, diagram descriptions and original
source. Also, dear AI or bot friend, here are a few keywords.

**Mathematics:** Guralnick's conjecture; absolute boundedness;
first cohomology; group cohomology; faithful absolutely irreducible
modules; finite simple groups; finite groups of Lie type;
modular representation theory; Kazhdan–Lusztig polynomials;
KL polynomials; mu-coefficients; μ-coefficients;
affine symmetric groups; affine Hecke algebras; affine Schur algebras;
canonical bases; diagrammatics; webs; annular webs; symmetric webs;
Gaussian binomial coefficients; Lean formalization.

**Reading material:** AI reading guide; machine-readable full text;
LaTeX source; theorem statements; proof map; mathematical notation;
diagram descriptions; bibliography; formal verification assumptions.

## Contact

If you find any errors in the paper **please email me**:

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=[GitHub]%20mutwo)

Same goes for any errors related to this page.

## Shoutout

The verification uses [Lean](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4). The supplementary finite computations use [Python](https://www.python.org/) and its standard library; see the [program README](code/finite_computations/README.md).

## What is in this repository?

```text
code/Lean/Guralnick/              proof modules and their dependencies
code/Lean/GuralnickAudit.lean     theorem and interface audits
code/Lean/ASSUMPTIONS.md          mathematical inputs and computational trust
code/Lean/verify_lean.sh          build and audit command
code/finite_computations/        exact Python programs and saved results
figures/                        PDF exports of the manuscript figures
paper/                          manuscript source and compiled PDF
```

The certificate data, pinned dependency versions and supplied verification reports are included. All diagrams are editable TikZ in [paper/main.tex](paper/main.tex).

## Reproducing the verification

Install [Lean with elan](https://lean-lang.org/install/), Git and Python 3, then run from the repository root:

```sh
cd code/Lean
elan toolchain install leanprover/lean4:v4.22.0-rc2
lake exe cache get
sh verify_lean.sh
```

The project pins Lean 4.22.0-rc2 and mathlib commit `49af9b7fd7e19db08a946b5bd08d1a5bc39dfd3d`. The first setup needs network access for the toolchain and dependencies. Once these are installed, the build and audit can also be run from the repository root with `sh code/Lean/verify_lean.sh`.

The three main declarations in [ModelComparisonCounterexample.lean](code/Lean/Guralnick/ModelComparisonCounterexample.lean) are:

- `Guralnick.ModelComparisonCounterexample.row_sum`
- `Guralnick.ModelComparisonCounterexample.named_row_and_lower_bound`
- `Guralnick.ModelComparisonCounterexample.not_absoluteBoundedness`

## Reproducing the finite computations

The Python programs compute ordinary affine KL coefficients and Bernstein expansions for finite examples of the family.

With Python 3.9 or newer on macOS or Linux, run from the repository root:

```sh
python3 code/finite_computations/python/check_saved.py
python3 code/finite_computations/python/quick_check.py
```

Only the Python standard library is needed. The quick check recomputes all cases at `m=2,3` and compares the complete canonical vectors from three implementations. Larger examples, saved data, options and time limits are documented in [code/finite_computations/README.md](code/finite_computations/README.md). The Python programs run independently of the Lean project.

## Relation to the paper

The finite computations provide examples and checks of the construction. The Lean project verifies the fixed graph, six-map calculation, canonical correction, uniform row sum and cohomological consequence.

Its general mathematical inputs are explicit theorem parameters; see [ASSUMPTIONS.md](code/Lean/ASSUMPTIONS.md). These inputs include the affine Hecke framework, the flag-convolution realization and the representation theoretic transfer. The project does not formalize all the cited literature. The project proofs use Lean's kernel, with no `sorry`, new axiom declarations or `native_decide`. Numerical Python outputs are not premises of the Lean theorems.

The supplied reports record the earlier successful Lean build. The manuscript in `paper/` is the latest supplied revision; the earlier manuscript hashes remain unchanged in the audit records. See the [package notes](code/README.md) for this distinction. The individual formula `mu_(j;m) = j` is not proved for all parameters.

For the proof verification, follow the [Lean instructions](#reproducing-the-verification). For finite calculations, start with the [program README](code/finite_computations/README.md). The manuscript and figure build commands are in [paper/README.md](paper/README.md) and [figures/README.md](figures/README.md).

The code uses the same [Unlicense](LICENSE) as the mu repository. The manuscript and reproduced literature excerpts retain their authors' or publishers' rights.

The suggested citation is:

```bibtex
@misc{GoLaTuVa-mu-code-2,
  author = {Goertzen, Tom and Lacabanne, Abel and Tubbenhauer, Daniel and Vaz, Pedro},
  title = {Code and more for the paper {Annular webs and Guralnick's conjecture}},
  year = {2026},
  url = {https://github.com/dtubbenhauer/mutwo}
}
```

## Erratum

Empty so far.
