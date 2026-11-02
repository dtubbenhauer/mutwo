# Andersen follow-up source files

These three page images support [the follow-up audit](../../audit-andersen-followup.md).
They do not contain the original 1986 article. The full PDFs, extracted text
and historical `provenance.json` were not included in the supplied package.
The original download and extraction commands are retained below.

The Andersen–Stroppel file is the **Aarhus preprint**, not the journal layout.
An incomplete author-site journal download was replaced by the complete
university preprint. Page references in the audit use the printed preprint
pages. No partial file is retained.

From this directory, the public downloads can be reproduced with:

```sh
curl -L --fail https://arxiv.org/pdf/2508.12898v1 -o Andersen2025.pdf
curl -L --fail https://data.math.au.dk/publications/pp/2003/imf-pp-2003-1.pdf -o AndersenStroppel2003.pdf
curl -L --fail https://arxiv.org/pdf/1610.07055v2 -o Luebeck2017.pdf
pdftotext -layout Andersen2025.pdf Andersen2025.txt
pdftotext -layout AndersenStroppel2003.pdf AndersenStroppel2003.txt
pdftotext -layout Luebeck2017.pdf Luebeck2017.txt
pdftoppm -f 15 -l 15 -scale-to 1600 -png -singlefile Andersen2025.pdf Andersen2025-p15
pdftoppm -f 19 -l 19 -scale-to 1600 -png -singlefile AndersenStroppel2003.pdf AndersenStroppel2003-p18
pdftoppm -f 11 -l 11 -scale-to 1600 -png -singlefile Luebeck2017.pdf Luebeck2017-p11
```

These commands require curl and Poppler. PNG bytes may vary with renderer
versions; hashes identify the images actually inspected in this audit.
The PDF contents are literature evidence, not inputs consumed by Lean.
The reproduced pages retain their authors' or publishers' rights and are
not covered by the repository's software license.
