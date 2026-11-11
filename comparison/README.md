# The common web and its individual coefficients

[Read the comparison note](../guralnick_comparison.pdf).

We use an annular web to compute a row sum of affine Kazhdan–Lusztig coefficients. Bowman, de la Fuente, Libedinsky and Plaza use a parabolic construction to compute the diagonal entry $\mu_{m;m}=m$. Both approaches disprove Guralnick’s conjecture in degree one. Bowman, de la Fuente, Libedinsky and Plaza also prove unboundedness for finite simple groups in every fixed positive cohomological degree. [Papers and source files](provenance/README.md)

Applying two normalized parabolic symmetrizers to their uncorrected product gives our six-stage annular web. In the note we keep the first $j$ canonical constituents before applying the symmetrizers, with the ambient rank fixed. We combine the support, multiplicities and degree bounds from our web calculation with their parabolic orbit estimates and a finite flag count. This gives the partial row sum, and consecutive differences give each entry,

$$
\sum_{i=1}^{j}\mu_{i;m}=\binom{j+1}{2},
\qquad
\mu_{j;m}=j\quad(1\le j\le m).
$$

We also identify the two finite tails as single canonical elements, compute the lower terms introduced by the simple-reflection chains, and give the hypotheses for the cohomological consequences.

## Contents

- [LaTeX source](report/comparison.tex) and [annular diagrams](report/webs.tex)
- [Finite canonical tails](report/finite-tails.tex) and [proof for the individual entries](report/partialrows.tex)
- [Cohomological consequences](report/implications.tex)
- [Exact calculations with level words](checks/README.md) and [with affine windows](independent_checks/README.md)

We used AI in preparing the note and both Python implementations. The note gives the proofs for all ranks. The programs compute finite examples using two descriptions of the spherical module. Our [Lean development](../code/Lean) verifies the row sum and cohomological result in our annular-web paper.

## Rebuild the PDF

From this directory, with a standard TeX Live installation, run

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build comparison.tex
cp build/comparison.pdf ../../guralnick_comparison.pdf
```

The source contains the editable TikZ figures. `latexmk` reruns LaTeX to resolve cross-references.

## Reproduce the affine-window checks

From this directory, with Python 3.10 or newer, run

```sh
python3 independent_checks/validate_engine.py
python3 independent_checks/finite_tail_checks.py
python3 independent_checks/normalized_partial_checks.py 2 3 4 5
```

These programs use the Python standard library and write the full canonical vectors to `independent_checks/output/`. The [recorded calculations](independent_checks/README.md) include the standard-coordinate comparisons, partial canonical expansions and degree bounds for $m=2,3,4,5$.
