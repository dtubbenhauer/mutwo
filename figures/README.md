# Figures

These are vector PDF exports of the figures in
[*Annular webs and Guralnick's conjecture*](../paper/main.pdf).
All editable drawing code is in [`paper/main.tex`](../paper/main.tex).
The exports preserve the drawings and their internal labels; figure captions
and page-layout wrappers are omitted.

| File | Figure in the paper |
| --- | --- |
| [`toroidal-closure.pdf`](toroidal-closure.pdf) | 1: The toroidal closure of the web graph |
| [`affine-permutations-m2.pdf`](affine-permutations-m2.pdf) | 2: The first two representatives, in one period and on the annulus |
| [`web-construction-m2-m3.pdf`](web-construction-m2-m3.pdf) | 3: Three stages of the webs for m=2 and m=3 |
| [`annular-family.pdf`](annular-family.pdf) | 4: The annular and cut-open forms of the same web |
| [`first-canonical-correction.pdf`](first-canonical-correction.pdf) | 5: The first canonical correction |
| [`heawood-graph.pdf`](heawood-graph.pdf) | 6: The Heawood graph in the plane and on a torus |
| [`heawood-moves.pdf`](heawood-moves.pdf) | 7: Six Whitehead moves from the closure to the Heawood embedding |
| [`annular-web.pdf`](annular-web.pdf) | The annular view from Figure 4, on its own |
| [`cut-open-web.pdf`](cut-open-web.pdf) | The cut-open view from Figure 4, on its own |

## Reproducing the figures

Install Python 3.10 or newer, [pypdf](https://pypdf.readthedocs.io/),
Ghostscript, and a LaTeX installation with the packages used by the paper
and the `preview` package. Then run from the repository root:

```sh
python3 figures/export_figures.py
```

The script reads the original TikZ and preamble from `paper/main.tex`,
compiles the figures, and crops the PDF pages with a small border.
It leaves the manuscript unchanged. The manuscript does not load these
exports: its diagrams remain inline TikZ.
