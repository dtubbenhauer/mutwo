#!/usr/bin/env python3
"""Build a conservative AI reading edition from this paper's self-contained TeX.

Python standard library + pandoc + pdflatex + pdftotext. No network access or TeX shell escape.
The supplied source is unchanged; the temporary compilation adds invisible labels.
This is a converter for this manuscript, not an arbitrary LaTeX parser.
Run from the repository root: python3 ai/tools/build_companion.py
Handwritten AI_README.md and diagrams.md must be reviewed after source changes.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

AI = Path(__file__).resolve().parents[1]
ROOT = AI.parent
BASE = "https://github.com/dtubbenhauer/mutwo/blob/main/"
RAW = "https://raw.githubusercontent.com/dtubbenhauer/mutwo/main/"
STMT = {"definition", "lemma", "theorem", "proposition", "corollary", "remark", "example", "question"}
MATH_ENVS = {"gather", "gather*", "align", "align*", "equation", "equation*", "multline", "multline*"}


def balanced(s, p, left="{", right="}"):
    assert s[p] == left, (p, s[p:p+80])
    depth = 1
    q = p + 1
    while q < len(s):
        if s[q] == "\\":
            q += 2
            continue
        if s[q] == left:
            depth += 1
        elif s[q] == right:
            depth -= 1
            if depth == 0:
                return s[p+1:q], q+1
        q += 1
    raise ValueError("Unbalanced group at " + str(p))


def skip(s, p):
    while p < len(s) and s[p].isspace():
        p += 1
    return p


def strip_comments(s):
    # Preserve offsets and newline positions for source pointers.
    return re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m[0]), s)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def anchor(s):
    return re.sub(r"[^a-z0-9_-]+", "-", s.lower()).strip("-")


def groups(s):
    out, p = [], 0
    while p < len(s):
        p = skip(s, p)
        if p >= len(s) or s[p] != "{":
            break
        val, p = balanced(s, p)
        out.append(val)
    return out


def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def run(cmd, **kw):
    p = subprocess.run(cmd, text=True, capture_output=True, **kw)
    if p.returncode:
        raise RuntimeError("Command failed: " + str(cmd) + "\n" + p.stdout[-4000:] + p.stderr[-4000:])
    return p


def parse_definitions(src):
    defs = {}
    pat = r"\\(?:newcommand|renewcommand|providecommand)\s*(?:\{\\([A-Za-z]+)\}|\\([A-Za-z]+))"
    for m in re.finditer(pat, src):
        name = m[1] or m[2]
        p = skip(src, m.end())
        nargs, default = 0, None
        if p < len(src) and src[p] == "[":
            val, p = balanced(src, p, "[", "]")
            nargs = int(val)
            p = skip(src, p)
            if src[p] == "[":
                default, p = balanced(src, p, "[", "]")
                p = skip(src, p)
        if p < len(src) and src[p] == "{":
            val, end = balanced(src, p)
            defs[name] = {"name": name, "nargs": nargs, "default": default,
                          "body": val, "start": m.start(), "end": end}
    picture_names = {k for k, d in defs.items() if re.search(r"\\(?:begin\{tikzpicture\}|draw\b|node\b)", d["body"])}
    for _ in range(len(defs)):
        added = {k for k, d in defs.items()
                 if any(n in picture_names for n in re.findall(r"\\([A-Za-z]+)", d["body"]))}
        if added <= picture_names:
            break
        picture_names |= added
    return defs, picture_names


def command_call(s, start, name, definition):
    p = start + len(name) + 1
    required = definition["nargs"]
    if definition["default"] is not None:
        required -= 1
        z = skip(s, p)
        if z < len(s) and s[z] == "[":
            _, p = balanced(s, z, "[", "]")
    for _ in range(required):
        p = skip(s, p)
        _, p = balanced(s, p)
    return p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--date", default="2026-11-03", help="Date of this companion snapshot, YYYY-MM-DD")
    parser.add_argument("--aux-cache", type=Path, help="Optional local cache for unchanged numbering compilation")
    parser.add_argument("--debug-dir", type=Path, help="Write intermediate conversion text for diagnosis")
    args = parser.parse_args()
    src = (AI / "source.tex").read_text()
    clean = strip_comments(src)
    def line(pos):
        return src.count("\n", 0, pos) + 1

    body_start = clean.index(r"\section{")
    body_end = clean.index(r"\end{document}")
    defs, pictures = parse_definitions(clean[:clean.index(r"\begin{document}")])
    environments = []
    stack = []
    for m in re.finditer(r"\\(begin|end)\{([^}]+)\}", clean):
        if m[1] == "begin":
            stack.append((m[2], m.start(), m.end()))
        elif stack and stack[-1][0] == m[2]:
            name, start, inner = stack.pop()
            environments.append({"name": name, "start": start, "inner": inner,
                                 "close": m.start(), "end": m.end()})
        else:
            raise ValueError("Environment nesting mismatch at source line " + str(line(m.start())))
    envs = sorted([e for e in environments if e["start"] >= body_start], key=lambda e: e["start"])
    labels = []
    for m in re.finditer(r"\\label\{([^}]+)\}", clean[body_start:body_end]):
        p = m.start() + body_start
        labels.append({"key": m[1], "pos": p, "end": m.end()+body_start, "anchor": anchor(m[1]), "line": line(p)})
    assert len({x["key"] for x in labels}) == len(labels)

    # Invisible labels also record numbers/pages for otherwise unlabelled statements.
    inserts = []
    statements = []
    for e in envs:
        if e["name"] not in STMT:
            continue
        p = skip(clean, e["inner"])
        opt = ""
        if clean[p] == "[":
            opt, p = balanced(clean, p, "[", "]")
        sid = f"ai-statement-{len(statements)+1:03d}"
        inserts.append((p, "\\label{"+sid+"}"))
        own = [x["key"] for x in labels if e["start"] <= x["pos"] < e["end"]]
        statements.append({"id": sid, "kind": e["name"], "heading_tex": opt,
                           "labels": own, "start": e["start"], "end": e["end"],
                           "inner": p, "close": e["close"]})
    sections, sec, sub = [], 0, 0
    for m in re.finditer(r"\\(section|subsection)(\*)?\{", clean[body_start:body_end]):
        start = body_start + m.start()
        title, end = balanced(clean, body_start + m.end()-1)
        kind = m[1]
        if not m[2]:
            if kind == "section":
                sec, sub = sec+1, 0
            else:
                sub += 1
        number = (str(sec) if kind == "section" else str(sec)+chr(64+sub)) if not m[2] else None
        sid = f"ai-section-{len(sections)+1:03d}"
        inserts.append((end, "\\label{"+sid+"}"))
        sections.append({"id": sid, "kind": kind, "title": title, "number": number, "start": start, "end": end})
    instrumented = src
    for p, value in sorted(inserts, reverse=True):
        instrumented = instrumented[:p] + value + instrumented[p:]
    compile_hash=hashlib.sha256(instrumented.encode()).hexdigest()
    cache=json.loads(args.aux_cache.read_text()) if args.aux_cache and args.aux_cache.exists() else {}
    if cache.get("compile_hash")==compile_hash:
        aux=cache["aux"]
    else:
        with tempfile.TemporaryDirectory(prefix="mutwo-ai-") as td:
            td = Path(td)
            (td/"numbered.tex").write_text(instrumented)
            for _ in range(2):
                run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "numbered.tex"], cwd=td)
            aux = (td/"numbered.aux").read_text()
        if args.aux_cache:write_json(args.aux_cache,{"compile_hash":compile_hash,"aux":aux})
    auxlabels = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}", aux):
        p = skip(aux, m.end())
        value, _ = balanced(aux, p)
        g = groups(value)
        if len(g)<2:continue
        auxlabels[m[1]] = {"number": g[0], "pdf_page": int(g[1]), "destination": g[3] if len(g)>3 else ""}
    for x in labels:
        x.update(auxlabels[x["key"]])
    labelmap = {x["key"]: x for x in labels}
    for s in statements + sections:
        s.update(auxlabels[s["id"]])
    # Starred headings inherit a counter; their structural number is intentionally omitted.
    for s in sections:
        if clean[s["start"]:s["end"]].startswith(r"\subsection*"):
            s["number"] = None

    # Check visible numbers in the supplied PDF; hyperref IDs depend on the TeX version.
    pdfpages=run(["pdftotext","-layout",str(AI/"source.pdf"),"-"]).stdout.split("\f")
    statement_page_checks=[]
    for s in statements:
        pat=re.compile(r"^\s*"+s["kind"].title()+r"\s+"+re.escape(s["number"])+r"(?:\.|\s*\()",re.M)
        found=[i+1 for i,page in enumerate(pdfpages) if pat.search(page)]
        if not found:raise ValueError("Statement not found in supplied PDF: "+s["kind"]+" "+s["number"])
        old=s["pdf_page"];s["pdf_page"]=found[0]
        statement_page_checks.append({"statement":s["kind"]+" "+s["number"],"compiled_page":old,"supplied_pdf_page":found[0]})
    for s in sections:
        if not s["number"]:continue
        pat=re.compile(r"^\s*"+re.escape(s["number"])+r"\.\s",re.M)
        found=[i+1 for i,page in enumerate(pdfpages) if pat.search(page)]
        if found:s["pdf_page"]=min(found,key=lambda n:abs(n-s["pdf_page"]))
    for x in labels:
        kind=x["destination"].split(".")[0]
        target=next((s for s in statements if s["kind"]==kind and s["number"]==x["number"]),None)
        if target:x["pdf_page"]=target["pdf_page"]
        elif kind in {"section","subsection"}:
            target=next((s for s in sections if s["number"]==x["number"]),None)
            if target:x["pdf_page"]=target["pdf_page"]
        elif kind in {"equation","figure"}:
            pat=re.escape("("+x["number"]+")") if kind=="equation" else r"Figure\s+"+re.escape(x["number"])+r"\."
            found=[i+1 for i,page in enumerate(pdfpages) if re.search(pat,page)]
            if found:x["pdf_page"]=min(found,key=lambda n:abs(n-x["pdf_page"]))

    bibliography = []
    bibpat = list(re.finditer(r"\\bibitem(?:\[([^\]]+)\])?\{([^}]+)\}", clean))
    for i, m in enumerate(bibpat):
        end = bibpat[i+1].start() if i+1 < len(bibpat) else clean.index(r"\end{thebibliography}", m.end())
        bibliography.append({"key": m[2], "citation_label_tex": m[1] or m[2],
                             "anchor": "bib-"+anchor(m[2]), "source_lines": [line(m.start()), line(end)-1],
                             "tex": src[m.end():end].strip(),
                             "urls": re.findall(r"\\(?:href|url)\s*\{([^}]+)\}", clean[m.end():end])})
    bibmap = {b["key"]: b for b in bibliography}

    # Replace each drawing by a marker, retaining exact source and invocation in the index.
    diagrams, replacements = [], []
    tikzs = [e for e in envs if e["name"] == "tikzpicture"]
    occupied = [(e["start"], e["end"]) for e in tikzs]
    candidates = [(e["start"], e["end"], "tikzpicture") for e in tikzs]
    for m in re.finditer(r"\\([A-Za-z]+)", clean[body_start:body_end]):
        name, p = m[1], body_start+m.start()
        if name not in pictures or any(a <= p < b for a,b in occupied):
            continue
        end = command_call(clean, p, name, defs[name])
        candidates.append((p, end, name))
    for i, (start, end, name) in enumerate(sorted(candidates), 1):
        did = f"D{i:03d}"
        macro_refs = sorted(set(re.findall(r"\\([A-Za-z]+)", clean[start:end])) & set(defs))
        record = {"id": did, "kind": name, "source_lines": [line(start), line(end)],
                  "tex": src[start:end], "macros": macro_refs}
        diagrams.append(record)
        replacements.append((start, end, f"AIDIAGRAM{did}END"))

    # Anchors are outside math/figures, so links remain valid when equations are fetched alone.
    anchor_at = collections.defaultdict(list)
    for x in labels:
        containing = [e for e in envs if e["start"] <= x["pos"] < e["end"]
                      and (e["name"] in STMT | MATH_ENVS | {"figure", "table"})]
        p = max(containing, key=lambda e:e["start"])["start"] if containing else x["pos"]
        anchor_at[p].append(x["anchor"])
        replacements.append((x["pos"], x["end"], ""))
    token_values, token_counter = {}, 0
    def token(value):
        nonlocal token_counter
        token_counter += 1
        key = f"AIPROTECTED{token_counter:06d}END"
        token_values[key] = value
        return key
    for s in sections:
        header = ("## " if s["kind"] == "section" else "### ")
        title = ((s["number"]+". ") if s["number"] else "") + s["title"]
        aid = ("section-"+s["number"].lower()) if s["number"] else anchor(s["title"])
        s["anchor"] = aid
        value = f'\n\n<a id="{aid}"></a>\n\n{header}{title}\n\n'
        value += f'<!-- Source: source.tex lines {line(s["start"])}; PDF page {s["pdf_page"]}. -->\n\n'
        replacements.append((s["start"], s["end"], "\n\n"+token(value)+"\n\n"))
    for s in statements:
        own = next((labelmap[k]["anchor"] for k in s["labels"] if labelmap[k]["number"] == s["number"]), s["id"])
        s["anchor"] = own
        p = s["inner"]
        caption = s["kind"].title()+" "+s["number"]
        heading = f"\n\n**{caption}.**"
        if s["heading_tex"]:
            heading += " ("+s["heading_tex"]+")"
        heading += f' [Source](source.tex#L{line(s["start"])}); [PDF p. {s["pdf_page"]}](source.pdf#page={s["pdf_page"]}).\n\n'
        if own == s["id"]:
            heading = f'<a id="{own}"></a>\n\n' + heading
        replacements.append((s["start"], p, "\n\n"+token(heading)+"\n\n"))
        replacements.append((s["close"], s["end"], "\n\n"))
    for p, names in anchor_at.items():
        value = "\n\n" + "\n".join(f'<a id="{a}"></a>' for a in names) + "\n\n"
        replacements.append((p, p, "\n\n"+token(value)+"\n\n"))

    # Bibliography handled separately; retain the exact TeX text as well as clickable URLs.
    bibbegin = next(e for e in envs if e["name"] == "thebibliography")
    bibmd = '\n\n<a id="references"></a>\n\n## References\n\n'
    for b in bibliography:
        label_plain = b["citation_label_tex"].replace(r'\"u', 'ü')
        bibmd += f'<a id="{b["anchor"]}"></a>\n\n### [{label_plain}] `{b["key"]}`\n\n'
        # Literal source is intentional: no publisher/DOI data is rewritten by a converter.
        bibmd += '```latex\n'+b["tex"]+'\n```\n\n'
        if b["urls"]:
            bibmd += " | ".join(f"[Link {j+1}]({u})" for j,u in enumerate(b["urls"]))+"\n\n"
    replacements.append((bibbegin["start"], bibbegin["end"], "\n\n"+token(bibmd)+"\n\n"))

    # Changes never overlap except zero-width anchors at the opening of a replaced block.
    replacements.sort(key=lambda r:(r[0], 0 if r[0]==r[1] else 1))
    pieces, cursor = [], body_start
    for a,b,value in replacements:
        if a < cursor:
            if a == b:
                raise ValueError("Anchor accidentally nested in removed content")
            # Labels inside a statement's optional heading are already rendered there.
            raise ValueError(f"Overlapping replacement at line {line(a)}: {src[a:b][:80]}")
        pieces.append(clean[cursor:a]); pieces.append(value); cursor=b
    pieces.append(clean[cursor:body_end])
    body = "".join(pieces)

    citations = []
    def cite(m):
        command, option, keys = m[1], m[2] or "", m[3]
        keys = [k.strip() for k in keys.split(",")]
        citations.extend(keys)
        links=[]
        for k in keys:
            b=bibmap[k]
            txt=b["citation_label_tex"].replace(r'\"u', 'ü')
            links.append(f'[{txt}](#{b["anchor"]})')
        return token("["+", ".join(links)+(", "+option if option else "")+"]")
    citepat=r"\\(cite|citep|citet)(?:\[([^\]]*)\])?\{([^}]+)\}"
    def ref(m):
        command, key = m[1], m[2]
        x = labelmap[key]
        dest = x["destination"].split(".")[0]
        prefix = {"section":"Section", "subsection":"Section", "figure":"Figure", "equation":"Equation"}.get(dest,dest.title())
        text = (prefix+" "+x["number"]) if command=="autoref" else ("("+x["number"]+")" if command=="eqref" else x["number"])
        return token(f'[{text}](#{x["anchor"]})')
    refpat=r"\\(autoref|eqref|ref)\{([^}]+)\}"
    body = re.sub(citepat,cite,body)
    body = re.sub(refpat,ref,body)
    # Optional statement headings are protected from Pandoc too; resolve their references.
    for key in list(token_values):
        token_values[key] = re.sub(refpat,ref,token_values[key])

    # Math is carried through as literal TeX, avoiding any Unicode/PDF reconstruction.
    mathblocks=[]
    pat=re.compile(r"(?<!\\)\$|(?<!\\)\\\[|(?<!\\)\\\(|(?<!\\)\\begin\{(?:gather\*?|align\*?|equation\*?|multline\*?)\}")
    out=[]; p=0
    while True:
        m=pat.search(body,p)
        if not m: break
        out.append(body[p:m.start()])
        start=m.end(); opener=m[0]
        if opener=="$":
            close=re.search(r"(?<!\\)\$",body[start:])
            if not close: raise ValueError("Unclosed inline math")
            stop=start+close.start(); end=start+close.end(); mode="inline"
        elif opener in (r"\[",r"\("):
            closer=r"\]" if opener==r"\[" else r"\)"
            stop=body.index(closer,start);end=stop+2;mode="display" if opener==r"\[" else "inline"
        else:
            env=re.search(r"\{([^}]+)\}",opener)[1]
            closer=r"\end{"+env+"}";stop=body.index(closer,start);end=stop+len(closer);mode="display"
        content=body[start:stop].strip()
        ds=re.findall(r"AIDIAGRAM(D\d+)END",content)
        content=re.sub(r"AIDIAGRAM(D\d+)END",lambda x:r"\text{["+x[1]+"]}",content)
        if opener.startswith(r"\begin"):
            content=opener+"\n"+content+"\n"+closer
        # Standard mathematical macro definitions are expanded literally; no drawing is guessed.
        for name in ("qbinom","Sym","Hom","Span","weval","webcoordinate"):
            d=defs[name]
            while (mm:=re.search(r"\\"+name+r"\b",content)):
                cp=mm.end(); vals=[]
                for _ in range(d["nargs"]):
                    cp=skip(content,cp);v,cp=balanced(content,cp);vals.append(v)
                replacement=d["body"]
                for j,v in reversed(list(enumerate(vals,1))):replacement=replacement.replace("#"+str(j),v)
                content=content[:mm.start()]+replacement+content[cp:]
        if mode=="display":
            # Fenced LaTeX keeps unusual mixed text/diagram displays exact and readable to tools.
            rendered="\n\n```latex\n"+content+"\n```\n\n"
        else:
            rendered="$"+content+"$"
        if ds:
            rendered += " "+"; ".join(f"[{d}](diagram-index.md#{d.lower()})" for d in dict.fromkeys(ds))
            if mode=="display":rendered+="\n\n"
        mathblocks.append({"mode":mode,"tex":content})
        out.append(token(rendered));p=end
    out.append(body[p:]);body="".join(out)
    body=re.sub(r"AIDIAGRAM(D\d+)END",lambda m:token(f'[{m[1]}: drawing](diagram-index.md#{m[1].lower()})'),body)
    # Remove layout wrappers outside protected math, retaining their contents.
    body=re.sub(r"\\begin\{(?:minipage)\}(?:\[[^\]]*\])?\{[^}]*\}","\n",body)
    body=re.sub(r"\\end\{minipage\}","\n",body)
    body=re.sub(r"\\(?:begin|end)\{figure\}(?:\[[^\]]*\])?","\n",body)
    body=re.sub(r"\\begin\{proof\}(?:\[([^\]]*)\])?",lambda m:"\n\n"+token("**"+(m[1] or "Proof")+".**")+"\n\n",body)
    body=body.replace(r"\end{proof}","\n\n"+token("*End of proof.*")+"\n\n")
    body=re.sub(r"\\(?:begingroup|endgroup|centering|raggedright|hfill|noindent|webdetailsfalse|webdetailstrue|smallskip|medskip|bigskip)", "", body)
    body=body.replace(r"\par", "\n\n")
    body=re.sub(r"\\looseness\s*=\s*-?\d+", "", body)
    body=re.sub(r"\\setlength\{[^}]*\}\{[^}]*\}", "", body)
    body=re.sub(r"\\(?:vspace|hspace)\*?\{[^}]*\}", " ", body)
    # Protect every remaining authored prose command that Pandoc might silently omit.
    # Main concern: caption contents, and repository paths in \repo.
    body=body.replace(r"\repo{",r"\texttt{")
    for command, prefix, suffix in [("caption","**Figure caption.** ",""),("resizebox","","")]:
        if command=="resizebox":continue
        while (m:=re.search(r"\\"+command+r"(?:\[[^\]]*\])?\{",body)):
            val,end=balanced(body,m.end()-1)
            body=body[:m.start()]+token(prefix)+val+suffix+body[end:]
    if args.debug_dir:
        args.debug_dir.mkdir(parents=True,exist_ok=True)
        (args.debug_dir/"preprocessed.tex").write_text(body)
        write_json(args.debug_dir/"tokens.json",token_values)
    p=run(["pandoc","-f","latex","-t","markdown+raw_html","--wrap=none"],input=body)
    if p.stderr.strip():
        raise ValueError("Pandoc reported a conversion warning: "+p.stderr)
    missing_tokens=set(re.findall(r"AIPROTECTED\d+END",body))-set(re.findall(r"AIPROTECTED\d+END",p.stdout))
    if missing_tokens:raise ValueError("Pandoc dropped protected content: "+str(sorted(missing_tokens)))
    if args.debug_dir:(args.debug_dir/"pandoc-output.md").write_text(p.stdout)
    md=p.stdout
    # Nested protected reference tokens can occur in headings; expand to a fixed point.
    for _ in range(6):
        new=re.sub(r"AIPROTECTED\d+END",lambda m:token_values[m[0]],md)
        if new==md:break
        md=new
    if "AIPROTECTED" in md or "AIDIAGRAM" in md:
        raise ValueError("Unexpanded reader marker")
    md=re.sub(r"\n{4,}","\n\n\n",md).strip()+"\n"
    # Small metadata header; full mathematical guide stays in one hand-maintained location.
    abstract=re.search(r"\\begin\{abstract\}([\s\S]*?)\\end\{abstract\}",src)[1].strip()
    header=f'''# Annular webs and Guralnick's conjecture — text reading edition

Tom Goertzen, Abel Lacabanne, Daniel Tubbenhauer and Pedro Vaz.

Companion snapshot: {args.date}. [Reading guide](../AI_README.md) · [exact TeX](source.tex) · [matching supplied PDF](source.pdf) · [statement and reference index](index.json) · [diagram explanations](diagrams.md).

{abstract}

This is a mechanically generated reading edition of the supplied manuscript, including its proofs and bibliography. Mathematical displays are literal LaTeX code blocks; inline mathematics uses LaTeX. The display fences are intentional: they preserve arrays, normalization and mixed text/diagram formulas without relying on a browser's math renderer. Common mathematical macros are expanded from their definitions. Drawing placeholders D001, D002, ... point to their exact source in the [diagram index](diagram-index.md); they are editorial identifiers, not mathematical variables. The [diagram explanations](diagrams.md) supply the main maps and relations in text. Layout-only material is simplified. The exact source and PDF determine the paper's statements.

The original statement numbers and equation labels are retained. The index records source lines, PDF pages and exact statement/proof source. It records explicit cross-references, not a mechanically verified logical dependency graph. The selected proof route is in the reading guide. See [manifest](manifest.json) for source hashes and conversion checks.

## Contents

'''
    for s in sections:
        if s["kind"]=="section":header+=f'- [{s["number"]}. {s["title"]}](#{s["anchor"]})\n'
    header+='- [References](#references)\n\n'
    (AI/"paper.md").write_text(header+md)
    # Exact statement/proof payloads permit independent extraction without trusting conversion.
    for si,s in enumerate(statements):
        proof=next((e for e in envs if e["name"]=="proof" and e["start"]>=s["end"]),None)
        next_stmt=statements[si+1] if si+1<len(statements) else None
        if proof and (next_stmt is None or proof["start"]<next_stmt["start"]) and not clean[s["end"]:proof["start"]].strip():
            proof_tex=src[proof["start"]:proof["end"]]
            proof_lines=[line(proof["start"]),line(proof["end"])]
        else:proof_tex=None;proof_lines=None
        context=next((x for x in reversed(sections) if x["start"]<s["start"]),None)
        s.update({"source_lines":[line(s["start"]),line(s["end"])],
                  "section":context["number"] if context else None,
                  "tex":src[s["start"]:s["end"]],"proof_tex":proof_tex,"proof_source_lines":proof_lines,
                  "explicit_references":re.findall(refpat,src[s["start"]:s["end"]]+(proof_tex or "")),
                  "citations":sorted({k.strip() for _,_,ks in re.findall(citepat,src[s["start"]:s["end"]]+(proof_tex or "")) for k in ks.split(",")})})
        for k in ("start","end","inner","close"):s.pop(k,None)
    for s in sections:
        s["source_line"]=line(s.pop("start"));s.pop("end",None)
    for x in labels:x.pop("pos");x.pop("end")
    macros={k:{"source_lines":[line(d["start"]),line(d["end"])],"arguments":d["nargs"],"optional_default":d["default"],"tex":src[d["start"]:d["end"]]} for k,d in defs.items() if any(k in d["macros"] for d in diagrams)}
    index={"schema_version":1,"snapshot_date":args.date,"source_tex_sha256":sha(AI/"source.tex"),
           "source_pdf_sha256":sha(AI/"source.pdf"),"notes":"Derived navigation data, not an independent proof certificate. Label numbers come from temporary compilation. Statement pages are checked against visible numbers in the supplied PDF. Hyperref destination strings are compilation diagnostics, not links into the supplied PDF. Statement and proof TeX are exact source slices. Explicit references need not be logical dependencies. Bibliography is transcribed, not a fresh audit. Directly used diagram macro definitions are included; nested dependencies and full drawing context remain in source.tex.",
           "sections":sections,"labels":labels,"statements":statements,"bibliography":bibliography,
           "diagrams":diagrams,"diagram_macros":macros}
    write_json(AI/"index.json",index)
    # Concise navigation per drawing occurrence; full source is available in index.json too.
    dm="# Diagram source index\n\n[Semantic explanations](diagrams.md) · [full text](paper.md) · [exact source](source.tex)\n\n"
    dm+="D001, D002, ... are reading-edition placeholders. Each record identifies an original TikZ block or macro invocation. The original source, including all macro definitions and surrounding scopes, is authoritative; the displayed source fragment alone may depend on that context. Exact fragments and macro definitions are also in `index.json`.\n\n"
    for d in diagrams:
        a,b=d["source_lines"]
        dm+=f'<a id="{d["id"].lower()}"></a>\n\n## {d["id"]}: {d["kind"]}\n\n'
        dm+=f'[Exact source, lines {a}–{b}](source.tex#L{a}-L{b}).\n\n'
        if d["kind"]=="ProofComparison":
            dm+='The diagram contains a two-column proof comparison. Its text is transcribed in the [comparison table](diagrams.md#finite-affine-comparison).\n\n'
        if d["kind"]!="tikzpicture":dm+='```latex\n'+d["tex"]+'\n```\n\n'
        if d["macros"]:
            dm+="Definitions: "+", ".join(f'[`{k}`](source.tex#L{macros[k]["source_lines"][0]})' for k in d["macros"])+".\n\n"
    (AI/"diagram-index.md").write_text(dm)
    # Section-sized fetches are generated, never edited independently.
    chunks=AI/"sections";chunks.mkdir(exist_ok=True)
    top=[s for s in sections if s["kind"]=="section"]
    boundaries=[md.index(f'<a id="{s["anchor"]}"></a>') for s in top]+[md.index('<a id="references"></a>')]
    chunkrecords=[]
    for i,s in enumerate(top):
        name=f'{int(s["number"]):02d}-{anchor(s["title"])}.md'
        chunk=md[boundaries[i]:boundaries[i+1]]
        chunk=re.sub(r"\]\(#([^)]+)\)",r"](../paper.md#\1)",chunk)
        chunk=re.sub(r"\]\((source\.tex|source\.pdf|diagram-index\.md)([^)]*)\)",r"](../\1\2)",chunk)
        intro=f'# {s["number"]}. {s["title"]}\n\nPart of *Annular webs and Guralnick\'s conjecture*, snapshot {args.date}. [Reading guide](../../AI_README.md) · [complete text](../paper.md). Mathematical displays retain literal LaTeX; drawing markers link to exact source.\n\n'
        (chunks/name).write_text(intro+chunk)
        chunkrecords.append({"section":s["number"],"file":"ai/sections/"+name})
    refchunk=md[boundaries[-1]:]
    (chunks/"08-references.md").write_text(refchunk)
    chunkindex=f'# Manuscript sections\n\nSnapshot {args.date}. [Reading guide](../../AI_README.md) · [complete text](../paper.md) · [exact source](../source.tex). These files are generated from the same source as the complete reading edition. They make it possible to retrieve one section at a time; they do not supply additional or independently maintained accounts.\n\n'
    for item in chunkrecords:
        secdata=next(s for s in top if s["number"]==item["section"])
        chunkindex+=f'- [{secdata["number"]}. {secdata["title"]}]({Path(item["file"]).name})\n'
    chunkindex+='- [References](08-references.md)\n'
    (chunks/"README.md").write_text(chunkindex)
    # Checks that address conversion risks: missing references, missing statements, lost math tokens.
    for s in statements:
        assert f'**{s["kind"].title()} {s["number"]}.**' in md
    for x in labels:
        assert f'id="{x["anchor"]}"' in md, x["key"]
    assert set(citations)<=set(bibmap)
    for d in diagrams:assert d["id"] in md,d["id"]
    assert md.count("*End of proof.*")==len([e for e in envs if e["name"]=="proof"])
    assert len(mathblocks)==sum(1 for value in token_values.values() if value.startswith("$") or value.startswith("\n\n```latex\n"))
    report={"snapshot_date":args.date,"section_files":chunkrecords,"statement_page_checks":statement_page_checks,
            "counts":{"sections":len(top),"subsections":len(sections)-len(top),"statements":len(statements),
                      "proofs":len([e for e in envs if e["name"]=="proof"]),"labels":len(labels),
                      "bibliography_entries":len(bibliography),"diagram_occurrences":len(diagrams),
                      "math_spans":len(mathblocks)},
            "checks":["Every numbered statement has its original number and exact source slice.",
                      "Every original label has a reading-edition anchor.",
                      "Every cited bibliography key resolves.",
                      "Every diagram occurrence has a source record and a reading-edition marker.",
                      "All proof environments are represented.",
                      "Every protected math/citation/reference token survives the prose conversion.",
                      "All statement page links are checked against visible statement numbers in the supplied PDF.",
                      "Math spans are protected from Pandoc and retain TeX, with documented macro/drawing substitutions."],
            "limits":["These are conversion checks, not a mathematical proof audit.","Handwritten reading guide and diagram explanations need review when the manuscript changes.","Compilation page pointers must be compared with the supplied PDF after revisions."]}
    write_json(AI/"build-report.json",report)
    print(json.dumps(report,ensure_ascii=False,indent=2))


if __name__=="__main__":main()
