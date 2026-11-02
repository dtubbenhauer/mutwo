# Lean verification and finite computations

See the [repository README](../README.md) for setup and run instructions.

- [Lean/](Lean/README.md) contains the formalization, pinned dependencies,
  certificates, audit scripts and supplied verification reports.
- [finite_computations/](finite_computations/README.md) contains the exact
  Python programs, saved results and reproduction instructions.

## Scope

The Lean project proves the uniform fixed-source affine KL row sum and its
eventual-characteristic cohomological consequence, conditional on explicit
general literature inputs. See [ASSUMPTIONS.md](Lean/ASSUMPTIONS.md).
Numerical Python outputs are not premises of these theorems. The individual
formula `mu_(j;m)=j` for all parameters remains conjectural.

## Supplied reports and current manuscript

The supplied `Lean/reports/verification.json` records a successful earlier
build and 293 principal declaration audits. The existing
`package-manifest.json` in this directory is the unchanged manifest of the
supplied code package, before this repository layout was assembled. The
root [package-manifest.json](../package-manifest.json) records the files in
the current archive and identifies the documentation changes separately.

The manuscript in [paper/main.tex](../paper/main.tex) is the latest supplied
revision, unchanged. Its SHA-256 is
`1cde49a28dff0602af99cbab38a7580781d7203d85846b678f245e4c1e8d0af2`.
The earlier manuscript reviewed by the Lean audit has SHA-256
`1f926a87b4000953c4c32b0995c844687ab68861100a9ce39b07a965308ca8a4`.
The old hashes in `Lean/certificates/manuscript-review.json` are preserved.
The historical source and recommendations were not supplied. This package
does not assert a new semantic comparison between the latest manuscript
and the formalization.

The historical verifier looks for that earlier manuscript at
`code/main.tex`. The current source is kept in `paper/`, so it is not
mistaken for the reviewed file. The Lean build does not need either
manuscript.

## Checks for this archive

Prepared 3 November 2026.

- All 249 Lean source files match the supplied verification record.
- The pinned toolchain, Lake configuration and dependency lock are unchanged.
- The 14 window certificates regenerate without changes.
- The Python saved-data check and fresh `m=2,3` quick checks pass.
- The unmodified manuscript compiles; separate figures are exported from
  its existing TikZ source.
- A fresh Lean build was not run while packaging: Lean was not installed in
  the packaging environment. Use the documented command to reproduce it.

The full proof and computation sources, saved data and original build
reports are retained. Documentation was adapted for this layout, with the
long Lean README retained as [formalization notes](Lean/formalization-notes.md).
Local caches, downloaded Lean/mathlib dependencies and temporary LaTeX
files are not included. All diagrams remain editable in the manuscript.
