"""Generate the preprint, proof notes and linked correspondence from their frozen sources."""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "source"
READER = "markdown+tex_math_dollars+tex_math_single_backslash+gfm_auto_identifiers-smart-superscript"
REPOSITORY = "https://github.com/CheyLoveday/erdos-365-subquarter-preprint"
BUNDLE = "https://relay.fullyjustified.net/default_bundle_v33.tar"
MARK = chr(96)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def run(args, *, data=None, cwd=ROOT, env=None, strict=True):
    call = subprocess.run(args, input=data, text=True, capture_output=True,
                          cwd=cwd, env=env, timeout=180, check=False)
    if call.returncode or (strict and call.stderr.strip()):
        raise RuntimeError(f"{args[0]} returned {call.returncode}\n{call.stderr}\n{call.stdout}")
    return call.stdout


def nodes(value, kind):
    if isinstance(value, dict):
        if value.get("t") == kind:
            yield value
        for child in value.values():
            yield from nodes(child, kind)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child, kind)


def parse(path):
    return json.loads(run(["pandoc", "--sandbox", "-f", READER, "-t", "json", str(path)]))


def rewrite(doc, mapping):
    rendered = copy.deepcopy(doc)
    steps = []
    for link in nodes(rendered["blocks"], "Link"):
        target = link["c"][2][0]
        if urlsplit(target).scheme or target.startswith("#"):
            continue
        destination = mapping[target]
        link["c"][2][0] = destination
        steps.append((target, destination))
    copyback = copy.deepcopy(rendered)
    for old, new in zip(nodes(doc["blocks"], "Link"), nodes(copyback["blocks"], "Link"), strict=True):
        new["c"][2] = old["c"][2]
    if copyback != doc:
        raise ValueError("Reader link projection changed source content")
    return rendered, steps


def render_pdf(out, build, release_tag):
    public = f"{REPOSITORY}/blob/{release_tag}/"
    source = SOURCE / "MANUSCRIPT.md"
    doc = parse(source)
    converted, links = rewrite(doc, {
        "LAMPORT_COMPANION.md#lp07": public + "PROOF_NOTES.md#lp07",
        "LAMPORT_COMPANION.md#lp16": public + "PROOF_NOTES.md#lp16",
        "SUPPLEMENT.md": public + "FORMAL_VERIFICATION.md",
    })
    displays = list(nodes(doc["blocks"], "Math"))
    tags = re.findall(r"\\tag\{([^}]+)\}", source.read_text())
    if len(set(tags)) != len(tags) or len(tags) != 31 or len(links) != 3:
        raise ValueError("Unexpected preprint tag or link inventory")
    encoded = json.dumps(converted, ensure_ascii=False)
    provenance = build / "provenance.tex"
    provenance.write_text(
        "\\section*{Source and verification}\n"
        "This generated preprint uses the frozen Markdown authoring snapshot.\\par\n"
        "\\noindent Source: \\path{source/MANUSCRIPT.md}.\\par\n"
        "\\noindent Source SHA-256: \\path{" + sha(source) + "}.\\par\n"
        "\\noindent Generate from the repository root: \\verb|python3 -B render.py|.\\par\n"
        "\\noindent The \\href{" + public + "FORMAL_VERIFICATION.md}{verification supplement}"
        " records the formal scope and receipt identities.\\par\n"
    )
    tex = run(
        ["pandoc", "-f", "json", "-t", "latex", "-s", "--wrap=none",
         "--template", str(SOURCE / "paper.latex"), "-A", str(provenance)],
        data=encoded,
    )
    build.joinpath("article.tex").write_text(tex)
    env = dict(os.environ, SOURCE_DATE_EPOCH=str(
        int(datetime(2026, 11, 23, tzinfo=timezone.utc).timestamp())
    ))
    run(["tectonic", "--only-cached", "--untrusted", "--bundle", BUNDLE,
         "--keep-logs", "--outdir", str(build), "article.tex"],
        cwd=build, env=env, strict=False)
    log = build.joinpath("article.log").read_text(errors="replace")
    defects = [line for line in log.splitlines() if any(
        issue in line for issue in ("Overfull", "Missing character", "Undefined control", "LaTeX Error")
    )]
    if defects:
        raise ValueError("\n".join(defects))
    pdf = out / "subquarter-preprint.pdf"
    pdf.write_bytes(build.joinpath("article.pdf").read_bytes())
    return {"math_nodes": len(displays), "equation_tags": tags,
            "mapped_links": links, "tex_layout_diagnostics": defects}


def tex_for_github(tex):
    tex = re.sub(r"(?<=\\)\n[ \t]*", " ", tex)
    tex = re.sub(r"\\operatorname\{([A-Za-z][A-Za-z0-9]*)\}", r"\\mathrm{\1}", tex)
    if r"\operatorname" in tex:
        raise ValueError("Unsupported operator name in GitHub math")
    return re.sub(r"\\tag\{([^}]+)\}", lambda m: r"\qquad \text{(" + m[1] + ")}", tex)


def github_math(node):
    if isinstance(node, list):
        return [github_math(child) for child in node]
    if not isinstance(node, dict):
        return node
    if node.get("t") == "Math":
        kind, original = node["c"]
        tex = tex_for_github(original)
        if kind["t"] == "DisplayMath":
            text = "\n" + MARK * 3 + "math\n" + tex + "\n" + MARK * 3 + "\n"
        else:
            text = "$" + MARK + tex + MARK + "$"
        return {"t": "RawInline", "c": ["markdown", text]}
    return {key: github_math(child) for key, child in node.items()}


def render_proof_notes(out):
    source = SOURCE / "LAMPORT_COMPANION.md"
    parsed = parse(source)
    goal = next(i for i, row in enumerate(parsed["blocks"])
                if row.get("t") == "Header" and row["c"][1][0] == "goal-and-quantifier-discipline")
    doc = dict(parsed, blocks=parsed["blocks"][goal:], meta={})
    # GitHub's PDF viewer opens at the first page. Locate the cited passages
    # in the freshly typeset paper so the visible labels follow its pagination.
    pdf_text = run(["pdftotext", "-layout", str(out / "subquarter-preprint.pdf"), "-"])
    pages = [" ".join(page.split()) for page in pdf_text.split("\f")]
    if "Generate from the repository root: python3 -B render.py." not in pdf_text:
        raise ValueError("The PDF must preserve spaces in its reproduction command")
    pdf_passages = {
        "MANUSCRIPT.md#proposition-42--specialized-internal-producer": "Integer relation lemma (also used in Section 7)",
        "MANUSCRIPT.md#real-bound": "the two positive prefactors satisfy",
    }
    for link in nodes(doc["blocks"], "Link"):
        passage = pdf_passages.get(link["c"][2][0])
        if passage is not None:
            matches = [number for number, page in enumerate(pages, 1) if passage in page]
            if len(matches) != 1:
                raise ValueError(f"Expected one PDF page for {passage!r}, found {matches}")
            link["c"][1].extend([{"t": "Space"}, {"t": "Str", "c": f"(PDF p. {matches[0]})"}])
    converted, links = rewrite(doc, {
        "SUPPLEMENT.md": "FORMAL_VERIFICATION.md#formal-variants",
        **{f"PROOF_MAP.md#{anchor}": f"source/PROOF_MAP.md#{anchor}" for anchor in (
            "forward-map-and-dependencies", "reverse-declaration-index", "historical-bindings-and-joins",
        )},
        "MANUSCRIPT.md": "subquarter-preprint.pdf",
        **dict.fromkeys(pdf_passages, "subquarter-preprint.pdf"),
    })
    content = run(["pandoc", "--sandbox", "-f", "json", "-t", "gfm+tex_math_dollars", "--wrap=none"],
                  data=json.dumps(github_math(converted), ensure_ascii=False))
    ids = {n["c"][1][0] for n in nodes(doc["blocks"], "Header")}
    if not {"lp00", "lp07", "lp16", "lp24"} <= ids:
        raise ValueError("Required proof-notes anchors missing")
    header = (
        "# Lamport proof notes\n\n"
        "Read the [preprint](subquarter-preprint.pdf) and [current verification supplement](FORMAL_VERIFICATION.md). "
        "These generated notes reproduce the technical sections of the frozen companion, beginning with its goal. "
        "Find the prerequisites, Lean declarations and contract dispositions in the [full proof map](source/PROOF_MAP.md).\n\n"
        "> Generated reading copy. Edit the authoring source to change the mathematical text.\n\n"
        "<!-- Source: source/LAMPORT_COMPANION.md\n"
        f"Source SHA-256: {sha(source)}\n"
        "Generation: python3 -B render.py\n-->\n\n"
    )
    out.joinpath("PROOF_NOTES.md").write_text(header + content)
    return {"math_nodes": len(list(nodes(doc["blocks"], "Math"))), "mapped_links": links}


def render_proof_map(out, lock):
    source = SOURCE / "PROOF_MAP.json"
    data = json.loads(source.read_bytes())
    for key, file in (("manuscript_sha256", "MANUSCRIPT.md"), ("companion_sha256", "LAMPORT_COMPANION.md")):
        if data[key] != sha(SOURCE / file):
            raise ValueError(f"Proof map refers to a different {file}")

    def steps(ids):
        return ", ".join(f"[{step}](../PROOF_NOTES.md#{step.lower()})" for step in ids) or "—"

    def declaration(name, location):
        path = Path(location["path"])
        relative = path.relative_to("lean").as_posix()
        file = ROOT / path
        if lock["lean_source_sha256"].get(relative) != sha(file):
            raise ValueError(f"Unbound Lean source {path}")
        lines = file.read_bytes().splitlines(keepends=True)
        first, end = location["line"], location["end_before_line"]
        if not 1 <= first < end <= len(lines) + 1:
            raise ValueError(f"Invalid source bounds for {name}")
        if sha256(b"".join(lines[first-1:end-1])).hexdigest() != location["span_sha256"]:
            raise ValueError(f"Stale declaration span for {name}")
        short = name.removeprefix("P0365Subquarter.")
        return f"[{MARK}{short}{MARK}](../{path.as_posix()}#L{first})"

    rows = [
        "# Manuscript and Lean proof map", "",
        "The [proof notes](../PROOF_NOTES.md) explain the argument. The tables trace each step to the "
        "article and the checked Lean source. Edges express mathematical prerequisites at the step level. "
        "The Lean links open the implementing declarations and their named contracts.", "",
        "> Generated, non-authoritative reading copy. Edit the authoring map and regenerate. "
        "The public input is [PROOF_MAP.json](PROOF_MAP.json), exported from "
        f"{MARK}{data['authoring_map_path']}{MARK} with upstream SHA-256 {MARK}{data['authoring_map_sha256']}{MARK}. "
        f"The public data SHA-256 is {MARK}{sha(source)}{MARK}. Regenerate with {MARK}python3 -B render.py{MARK}.", "",
        "## Forward map and dependencies", "",
        "| Proof step | Article source | Inputs | Used by |", "| --- | --- | --- | --- |",
    ]
    for step in data["steps"]:
        article = ", ".join(f"[§{a['number']}](MANUSCRIPT.md#{a['anchor']})" for a in step["manuscript_sections"])
        users = [other["id"] for other in data["steps"] if step["id"] in other["depends_on"]]
        rows.append(f"| {steps([step['id']])} · {step['title']} | {article} | {steps(step['depends_on'])} | {steps(users)} |")

    rows += ["", "## Reverse declaration index", "",
             "Definitions specify objects and contracts. Theorem rows link to proofs. Each linked source span "
             "is checked against the frozen candidate during generation.", "",
             "| Declaration | Kind and role | Named target | Step | Contracts |", "| --- | --- | --- | --- | --- |"]
    for row in data["declarations"]:
        impl = declaration(row["name"], row["source"])
        target = declaration(row["target"], row["target_source"]) if row["target"] else "—"
        obligations = ", ".join(row["obligations"]) or "—"
        rows.append(f"| {impl} | {row['kind']} · {row['role'].replace('_', ' ')} | {target} | {steps([row['step']])} | {obligations} |")

    rows += ["", "## Historical bindings and joins", "",
             "The disposition records what became of each earlier contract. The frozen data also names "
             "the implementing, replacement and consuming declarations. Seven literal contracts are unused on the selected route.", "",
             "| Contract | Selected disposition | Producing steps | Consuming steps |", "| --- | --- | --- | --- |"]
    for row in data["obligations"]:
        title = row["title"].replace("|", "/")
        disposition = row["disposition"].lower().replace("_", " ")
        rows.append(f"| {MARK}{row['id']}{MARK} · {title} | {disposition} | {steps(row['steps'])} | {steps(row['consumer_steps'])} |")
    rows += ["", "Two annotations qualify the inherited contract wording.", ""]
    rows.extend(f"- {MARK}{row['id']}{MARK} — {row['note']}" for row in data["historical_text_annotations"])
    destination = out / "source" / "PROOF_MAP.md"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join([*rows, ""]))
    return {key: len(data[key]) for key in ("steps", "declarations", "obligations")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT)
    args = parser.parse_args()
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    lock = json.loads(ROOT.joinpath("sources.json").read_bytes())
    for file, digest in lock["source_sha256"].items():
        if sha(SOURCE / file) != digest:
            raise ValueError(f"Frozen source changed: {file}")
    for tool in ("pandoc", "tectonic"):
        if run([tool, "--version"]).splitlines()[0] != lock[tool + "_version"]:
            raise ValueError(f"Use the locked {tool} version")
    with TemporaryDirectory(prefix="subquarter-preprint-") as temporary:
        pdf = render_pdf(out, Path(temporary), lock["release_tag"])
    notes = render_proof_notes(out)
    mapping = render_proof_map(out, lock)
    print(json.dumps({"pdf": pdf, "proof_notes": notes, "proof_map": mapping,
                      "outputs": {name: sha(out / name) for name in (
                          "subquarter-preprint.pdf", "PROOF_NOTES.md", "source/PROOF_MAP.md")}}, indent=2))


if __name__ == "__main__":
    main()
