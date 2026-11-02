# Primary-source snapshots

These files support [audit-primary-transfer.md](../audit-primary-transfer.md).
They are literature, not Lean proofs or computational certificates. The
five page images in this directory are included as supplied. The full
PDFs, extracted text and historical `provenance.json` were not included in
the supplied package. The audit documents retain the checked page numbers
and access limitations; `affine/provenance.json` is a separate supplied record.

The original audit retrieved `AJS1994.pdf`, `Jantzen1985-I.pdf`,
`Steinberg1963.pdf` and `Steinberg1967-Yale.pdf`. Its Andersen publisher
response was metadata only. Neither that response nor an Andersen full-text
PDF is included here. The BNP PDF and screenshot referred to by the audit
were held in the historical `RevisedWeb/investigation/root/` workspace and
were not supplied. These literature files are not Lean build dependencies.

From this directory, the downloads can be reproduced with:

```sh
curl -L --fail -o AJS1994.pdf https://www.numdam.org/item/AST_1994__220__1_0.pdf
curl -L --fail -o Jantzen1985-I.pdf https://archive.mpim-bonn.mpg.de/id/eprint/607/1/preprint_1985_9.pdf
curl -L --fail -o Steinberg1963.pdf https://www.cambridge.org/core/services/aop-cambridge-core/content/view/02AE5498AF62BCAB6B313C75016E6015/S0027763000011016a.pdf/representations_of_algebraic_groups.pdf
curl -L --fail -o Steinberg1967-Yale.pdf https://www.math.utah.edu/~ptrapa/math-library/steinberg/steinberg-yale-notes.pdf
```

Text extraction uses Poppler's `pdftotext -layout`, for example:

```sh
pdftotext -layout AJS1994.pdf AJS1994.txt
pdftoppm -f 232 -l 232 -scale-to 1800 -png -singlefile AJS1994.pdf AJS1994-p229
```

The other image page selections are identified by their filenames. Extracted
text has OCR and mathematical-symbol errors. The included five page images
were inspected; they take precedence over corrupt inequalities or missing
formulas in the text. In particular AJS §16.24 restricts its unprimed Weyl
index, and Steinberg p.45 permits the simple-coroot label `p−1`.

The literature and reproduced page images retain their original authors'
or publishers' copyright and distribution terms. The repository's software
license does not apply to them.
