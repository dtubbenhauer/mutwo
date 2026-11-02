#!/usr/bin/env python3
"""Export the manuscript's seven figures as cropped vector PDFs.

Run from the repository root:
    python3 figures/export_figures.py

Requires Python 3.10+, pypdf, pdfLaTeX (with the paper's packages and preview),
and Ghostscript. All drawing code is read from paper/main.tex; that file is
never modified. Captions and floating/page-layout wrappers are omitted.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

FIGURES = (
    ("fig:toroidal-closure", "toroidal-closure"),
    ("fig:intro-example", "affine-permutations-m2"),
    ("fig:intro-affine-construction", "web-construction-m2-m3"),
    ("fig:intro-annular-family", "annular-family"),
    ("fig:intro-critical-correction", "first-canonical-correction"),
    ("fig:heawood", "heawood-graph"),
    ("fig:heawood-moves", "heawood-moves"),
)


def strip_command(text: str, command: str) -> str:
    """Remove a braced LaTeX command, respecting nested braces."""
    pattern = re.compile(r"\\" + re.escape(command) + r"\s*(?:\[[^\]]*\]\s*)?\{")
    while match := pattern.search(text):
        depth, end = 1, match.end()
        while end < len(text) and depth:
            if text[end] in "{}" and (end == 0 or text[end - 1] != "\\"):
                depth += 1 if text[end] == "{" else -1
            end += 1
        if depth:
            raise ValueError(f"Unbalanced argument of \\{command}")
        text = text[:match.start()] + text[end:]
    return text


def figure_body(block: str) -> str:
    body = re.sub(r"^\\begin\{figure\}(?:\[[^\]]*\])?", "", block)
    body = body.removesuffix(r"\end{figure}")
    body = strip_command(strip_command(body, "caption"), "label")
    body = re.sub(r"\\begin\{minipage\}(?:\[[^\]]*\])?\{[^}]*\}", "", body)
    body = body.replace(r"\end{minipage}", "")
    body = re.sub(r"\\setlength\{\\captionindent\}\{[^}]*\}", "", body)
    body = body.replace(r"\hfill", "")
    return body.strip()


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(
            "Command failed: " + " ".join(command) + "\n"
            + "\n".join((result.stdout + result.stderr).splitlines()[-45:])
        )
    return result


def main() -> None:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=here.parent / "paper" / "main.tex")
    parser.add_argument("--output", type=Path, default=here)
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    for program in ("pdflatex", "gs"):
        if shutil.which(program) is None:
            raise SystemExit(f"Required program not found: {program}")
    try:
        from pypdf import PdfReader, PdfWriter
        from pypdf.generic import RectangleObject
    except ImportError as error:
        raise SystemExit("Install pypdf first: python3 -m pip install pypdf") from error

    text = source.read_text(encoding="utf-8")
    preamble, _ = text.split(r"\begin{document}", 1)
    blocks = re.findall(r"\\begin\{figure\}(?:\[[^\]]*\])?.*?\\end\{figure\}", text, re.S)
    exports: list[tuple[str, str]] = []
    for label, name in FIGURES:
        matches = [block for block in blocks if r"\label{" + label + "}" in block]
        if len(matches) != 1:
            raise ValueError(f"Expected one figure labeled {label}, found {len(matches)}")
        exports.append((name, figure_body(matches[0])))

    # Two useful separate views from Figure 4, using exactly its drawing macros.
    exports.append(("annular-web", r"\begingroup\webdetailsfalse\RmAnnulus[.70]\endgroup"))
    family_body = next(body for name, body in exports if name == "annular-family")
    cut_open = re.search(r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", family_body, re.S)
    if cut_open is None:
        raise ValueError("Could not locate the cut-open diagram in Figure 4")
    exports.append(("cut-open-web", r"\begingroup\webdetailsfalse" + cut_open[0] + r"\endgroup"))

    document = preamble + r"""
\usepackage[active,tightpage]{preview}
\setlength{\PreviewBorder}{6pt}
\begin{document}
\pagestyle{empty}
"""
    for _, body in exports:
        document += "\n\\begin{preview}\n\\begin{minipage}{\\linewidth}\n"
        document += body + "\n\\end{minipage}\n\\end{preview}\n"
    document += r"\end{document}" + "\n"

    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="mutwo-figures-") as temporary:
        work = Path(temporary)
        (work / "figures.tex").write_text(document, encoding="utf-8")
        run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "figures.tex"], work)
        bounds_result = run(["gs", "-q", "-dNOPAUSE", "-dBATCH", "-sDEVICE=bbox", "figures.pdf"], work)
        bounds = re.findall(r"%%HiResBoundingBox: ([^\r\n]+)", bounds_result.stderr)
        reader = PdfReader(work / "figures.pdf")
        if len(reader.pages) != len(exports) or len(bounds) != len(exports):
            raise ValueError("The number of output pages does not match the figure list")
        for page, bound, (name, _) in zip(reader.pages, bounds, exports):
            left, bottom, right, top = map(float, bound.split())
            margin = 5.0  # PDF points; keep labels and arrowheads safely inside the page.
            page.mediabox = RectangleObject((left-margin, bottom-margin, right+margin, top+margin))
            page.cropbox = page.mediabox
            writer = PdfWriter()
            writer.add_page(page)
            writer.add_metadata({"/Title": name.replace("-", " "), "/Creator": "Exported from paper/main.tex"})
            destination = output / f"{name}.pdf"
            with destination.open("wb") as stream:
                writer.write(stream)
            print(destination.name)


if __name__ == "__main__":
    main()
