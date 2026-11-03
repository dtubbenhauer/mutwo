#!/usr/bin/env python3
"""Refresh companion hashes without claiming a new editorial or mathematical review."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AI = ROOT / "ai"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--date", required=True, help="Snapshot date, YYYY-MM-DD")
    args = parser.parse_args()
    current = AI / "manifest.json"
    previous = json.loads(current.read_text()) if current.exists() else {}
    review = previous.get("editorial_review", {
        "date": "2026-11-03",
        "source_tex_sha256": "3696b347b10a1894851e28af60692913dd8b7f22c27bc8139b234178a164f869",
        "source_pdf_sha256": "33bcabf73ed4b77afc34c3674e7de171161a727e4d1f9e1c1a8185fb66979498",
        "scope": "Reading guide and diagram descriptions checked for consistency with the supplied manuscript. This is not a mathematical proof audit or a fresh Lean build."
    })
    texhash, pdfhash = digest(AI / "source.tex"), digest(AI / "source.pdf")
    report = json.loads((AI / "build-report.json").read_text())
    index = json.loads((AI / "index.json").read_text())
    if index["source_tex_sha256"] != texhash or index["source_pdf_sha256"] != pdfhash:
        raise ValueError("The generated index is stale. Rebuild it before updating the manifest.")
    hand_files = ["AI_README.md", "llms.txt", "CITATION.cff", "ai/diagrams.md", "ai/toroidal-closure.json", "ai/UPLOAD.md"]
    files=[]
    for path in sorted(ROOT.rglob("*")):
        if not path.is_file() or path == current or "__pycache__" in path.parts:
            continue
        relative=path.relative_to(ROOT).as_posix()
        # Only enumerate this companion, not an existing repository around it.
        if not (relative.startswith("ai/") or relative in {"AI_README.md","llms.txt","CITATION.cff"}):
            continue
        files.append({"path":relative,"bytes":path.stat().st_size,"sha256":digest(path)})
    manifest={
        "schema_version": 1,
        "title": "Annular webs and Guralnick's conjecture — AI reading companion",
        "authors_of_paper": ["Tom Goertzen","Abel Lacabanne","Daniel Tubbenhauer","Pedro Vaz"],
        "snapshot_date":args.date,
        "repository":"https://github.com/dtubbenhauer/mutwo",
        "entry_point":"AI_README.md",
        "source":{
            "tex":"ai/source.tex", "tex_sha256":texhash,
            "pdf":"ai/source.pdf", "pdf_sha256":pdfhash,
            "initial_supplied_tex_filename":"main(20261103-022919).tex",
            "initial_supplied_pdf_filename":"Affine_mu(9).pdf",
            "authority":"The supplied manuscript source and PDF determine the mathematical statements. The companion provides reading and retrieval aids."
        },
        "repository_inspection":{
            "date":"2026-11-03", "default_branch":"main",
            "observed_commit":"5d196bcd502c93b0ae9a54d510228edf0668102a",
            "observed_commit_time_utc":"2026-11-02T21:53:34Z",
            "observed_paper_tex_path":"paper/main.tex",
            "observed_paper_tex_sha256":"1cde49a28dff0602af99cbab38a7580781d7203d85846b678f245e4c1e8d0af2",
            "note":"The observed repository manuscript differs from the supplied snapshot. New companion files do not exist at this old commit. Lean files and reports retain their own provenance."
        },
        "editorial_review":review,
        "needs_editorial_review":texhash!=review["source_tex_sha256"] or pdfhash!=review["source_pdf_sha256"],
        "hand_maintained_files":hand_files,
        "generated_text":"ai/paper.md",
        "section_files":report["section_files"],
        "conversion_counts":report["counts"],
        "conversion_checks":report["checks"],
        "conversion_notes":[
            "Source files are byte-for-byte copies of the supplied originals in this initial package.",
            "Displayed mathematics is literal LaTeX; common mathematical macros are expanded from their definitions.",
            "Drawing occurrences are represented by D001... markers. Exact snippets and direct macro definitions are indexed; all dependencies remain in the source.",
            "Section files are generated from the same text and are not independently edited.",
            "Statement numbers come from compilation. Statement page numbers are checked against visible headings in the supplied PDF.",
            "The bibliography is transcribed from the manuscript; this task does not independently certify every bibliographic entry.",
            "Hashes identify files; they are not proof certificates. No Lean build is claimed by this package.",
            "No new license is assigned to the manuscript, and publication identifiers are not invented."
        ],
        "files":files
    }
    current.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps({"files":len(files),"needs_editorial_review":manifest["needs_editorial_review"],"tex_sha256":texhash,"pdf_sha256":pdfhash}))


if __name__ == "__main__":main()
