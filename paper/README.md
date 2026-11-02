# Annular webs and Guralnick's conjecture

`main.tex` is the supplied manuscript, unchanged. It contains the complete
text, bibliography and editable TikZ diagrams. `main.pdf` was compiled from
this source for the repository.

With a TeX Live installation including the packages listed in the preamble,
run from the repository root:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

No external bibliography or figure files are needed. The separate PDF
exports in [figures/](../figures/README.md) are provided for reuse; the paper
does not load them.

The Lean audit records refer to an earlier reviewed manuscript. They are
preserved as supplied and do not certify that this later manuscript is
identical to the reviewed version. See [the package notes](../code/README.md).
