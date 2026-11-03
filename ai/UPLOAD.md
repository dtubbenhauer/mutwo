# Adding the AI companion to mutwo

Copy the contents of this package into the repository root, preserving the `ai/` directory. The root entry files are `AI_README.md`, `llms.txt` and `CITATION.cff`. All other companion material lives under `ai/`.

The package is an addition to the repository inspected on 2026-11-03. It supplies the exact attached manuscript as `ai/source.tex` and `ai/source.pdf`, so its source links and page references identify one consistent snapshot. The inspected `paper/main.tex` differed slightly from the attachment. The manifest records both hashes and the inspected repository commit. The existing repository README is edited by adding the short paragraph below.

## README addition

Place this after the introductory description of the paper:

```markdown
## Reading the paper with an AI agent

Start with the [AI reading guide](AI_README.md). It links to the complete
text, precise statements, proof dependencies, notation, diagram descriptions
and the matching manuscript source.

[Raw guide](https://raw.githubusercontent.com/dtubbenhauer/mutwo/main/AI_README.md)
· [Full text](ai/paper.md)
```

## Link in the paper

The source already loads `hyperref`. A short version is:

```latex
If you are an AI agent, start with the
\href{https://github.com/dtubbenhauer/mutwo/blob/main/AI_README.md}
{AI reading guide}.
```

A visible URL is more robust when a PDF extractor keeps printed text but loses hyperlink annotations. For that version use:

```latex
For AI readers: a text version, proof map and diagram descriptions are at
\url{https://github.com/dtubbenhauer/mutwo/blob/main/AI_README.md}.
```

Both links become valid after the files are uploaded to the `main` branch. The guide includes raw-text links for tools that cannot use the GitHub page. No files have been published by preparing this package.

For an archived paper version, upload the companion first, open `AI_README.md` on GitHub and press `y` to obtain a permalink to that uploaded revision. A branch link follows later updates; a commit link preserves the specific version. Do not use the old inspected commit for these new files. The guide labels its explicit raw URLs as current-branch links; for a version-specific raw request, replace `main` with the same commit used in the permalink.

## Keeping it synchronized

After changing the manuscript, update the matching `ai/source.tex` and `ai/source.pdf`, then run from the repository root:

```sh
python3 ai/tools/build_companion.py --date YYYY-MM-DD
```

The converter requires Python 3, Pandoc, Poppler (`pdftotext`), and a TeX installation able to compile the manuscript. It uses a temporary copy for statement labels and compilation; it does not modify the source files, use the network or enable TeX shell escape. It regenerates `paper.md`, section files, `index.json`, the drawing source index and the build report. The exact source and PDF remain available if a future TeX edit is outside the converter's supported syntax.

The converter is specific to this manuscript. It intentionally preserves displayed mathematics as literal LaTeX, so an unusual formula is not silently flattened or dropped. The statement index includes exact source slices as an additional route to the text. Bibliographic records are transcribed from the manuscript rather than independently updated.

Review `AI_README.md`, `ai/diagrams.md`, and `ai/toroidal-closure.json` after mathematical or diagram changes. They contain explanatory material and are not regenerated from TeX. Check equation/statement numbers and page references against the new PDF. Update `CITATION.cff` when a DOI, arXiv identifier or publication record becomes available. Then refresh the file hashes:

```sh
python3 ai/tools/update_manifest.py --date YYYY-MM-DD
```

`build-report.json` describes conversion checks. It is not a mathematical proof certificate, a bibliography audit or a fresh Lean build. Existing Lean audit reports retain their own version information. The manifest marks whether the current source hashes match the last recorded editorial review.

## Discoverability

The PDF link, the prominent repository README link, the title and author names, and direct text files provide the practical route into the companion. `llms.txt` supplies an additional small navigation file. It follows a proposal; it does not guarantee discovery or indexing, and a repository file does not set GitHub's crawler policy.

A root `CITATION.cff` is recognized by GitHub's citation interface. The preferred citation is the manuscript, with no invented journal, DOI or arXiv identifier. No new license is assigned to the manuscript by this companion.

An author-homepage link to the same guide is also useful. For a static homepage, an ordinary link is enough:

```html
<a href="https://github.com/dtubbenhauer/mutwo/blob/main/AI_README.md">AI reading guide and full text</a>
```

There is no need to add a separate website, special access service or `AGENTS.md` for reading this paper. The latter convention is intended for repository instructions to coding agents.

## Primary documentation

- [The llms.txt proposal](https://llmstxt.org/).
- [GitHub README links](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-readmes).
- [GitHub citation files](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files).
- [GitHub permanent links](https://docs.github.com/en/repositories/working-with-files/using-files/getting-permanent-links-to-files).
- [Google Search guidance on generative AI features](https://developers.google.com/search/docs/fundamentals/ai-optimization-guide), which distinguishes useful accessible content from unsupported claims about special AI markup.
- [AGENTS.md scope](https://agents.md/).
