#!/usr/bin/env python3
"""Compile the manuscript and retain the bibliography for a source-only submission."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "paper" / "tex"
LOCAL = ROOT / ".local"
BUILD = LOCAL / "build" / "paper"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources(source: Path = SOURCE) -> dict[str, str]:
    return {p.relative_to(source).as_posix(): digest(p)
            for p in sorted(source.rglob("*"))
            if p.is_file() and p.suffix in {".tex", ".bib"}}


def local_submission_source() -> tuple[Path, dict[str, str]]:
    """Read local identity data without embedding it in public source or tools."""
    private = LOCAL / "arxiv"
    metadata_path = private / "metadata.json"
    if not metadata_path.is_file():
        raise SystemExit("Create ignored .local/arxiv/metadata.json with author, email, and affiliation strings first.")
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    if any(not isinstance(metadata.get(key, ""), str) for key in ("author", "email", "affiliation")):
        raise SystemExit("Submission metadata fields must be strings.")
    if not metadata.get("author", "").strip():
        raise SystemExit("Submission author must not be empty.")
    email = metadata.get("email", "")
    if email and not re.fullmatch(r"[A-Za-z0-9._+\-]+@[A-Za-z0-9.\-]+", email):
        raise SystemExit("Use a plain email address in local submission metadata.")
    escapes = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
               "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    def tex(value: str) -> str:
        return "".join(escapes.get(char, char) for char in value)
    shared = sources()
    target = private / "tex"
    target.mkdir(parents=True, exist_ok=True)
    extra = set(sources(target)) - set(shared)
    if extra:
        raise SystemExit(f"Unexpected files in generated submission source: {sorted(extra)}")
    for relative in shared:
        output = target / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE / relative, output)
    lines = ["% Local submission metadata; this entire project is ignored by Git."]
    for macro, field in (("paperauthor", "author"), ("paperaffiliation", "affiliation"), ("paperemail", "email")):
        lines.append("\\newcommand*{\\" + macro + "}{" + tex(metadata.get(field, "")) + "}")
    (target / "metadata.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return target, shared


def submission_archive(source: Path, build: Path, before: dict[str, str]) -> None:
    files = {name: (source / name).read_bytes() for name in before}
    files["main.bbl"] = (build / "main.bbl").read_bytes()
    target = source.parent / "arxiv-source.tar.gz"
    with target.open("wb") as output, gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=1792627200) as compressed:
        with tarfile.open(fileobj=compressed, mode="w") as archive:
            for name, data in sorted(files.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 1792627200
                archive.addfile(info, io.BytesIO(data))
    with tarfile.open(target, "r:gz") as archive:
        restored = {entry.name: archive.extractfile(entry).read() for entry in archive.getmembers()}
    if restored != files:
        raise SystemExit("Submission archive round-trip mismatch.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition", choices=["public", "arxiv"], default="public",
                        help="The submission edition reads identity only from the ignored private directory.")
    parser.add_argument("--engine", choices=["auto", "latexmk", "pdflatex", "tectonic"], default="auto")
    parser.add_argument("--compiler", help="Explicit compiler executable (also select --engine).")
    parser.add_argument("--offline", action="store_true", help="For Tectonic, use only already cached packages.")
    args = parser.parse_args()
    engine = args.engine
    if args.compiler and engine == "auto":
        parser.error("--compiler requires an explicit --engine")
    if engine == "auto":
        engine = next((e for e in ("latexmk", "tectonic", "pdflatex") if shutil.which(e)), "")
    executable = args.compiler or (shutil.which(engine) if engine else None)
    if not executable:
        parser.error("Install TeX Live (latexmk and BibTeX) or Tectonic, or pass --engine and --compiler.")
    executable = str(Path(executable).resolve())
    source = SOURCE
    shared = sources()
    if args.edition == "arxiv":
        source, shared = local_submission_source()
    before = sources(source)
    build = BUILD if args.edition == "public" else LOCAL / "arxiv" / "build"
    pdf = ROOT / "paper" / "manuscript.pdf" if args.edition == "public" else source.parent / "manuscript.pdf"
    build.mkdir(parents=True, exist_ok=True)
    # Work on a fresh source copy: a failed run cannot validate stale output.
    with tempfile.TemporaryDirectory(prefix="compile-", dir=build) as directory:
        work = Path(directory)
        for relative in before:
            target = work / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / relative, target)
        if engine == "tectonic":
            commands = [[executable, "--untrusted", "--keep-intermediates", "--keep-logs"]
                        + (["--only-cached"] if args.offline else []) + ["main.tex"]]
        elif engine == "latexmk":
            commands = [[executable, "-norc", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "main.tex"]]
        else:
            bibtex = shutil.which("bibtex")
            if not bibtex:
                parser.error("The pdflatex workflow also requires bibtex on PATH.")
            latex = [executable, "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "main.tex"]
            commands = [latex, [bibtex, "main"], latex, latex]
        run_log = []
        for command in commands:
            result = subprocess.run(command, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            run_log.append(result.stdout)
            if result.returncode:
                (build / "compiler-output.log").write_text("\n".join(run_log), encoding="utf-8")
                raise SystemExit(result.stdout + "\nCompilation failed; existing release PDF was not replaced.")
        if before != sources(source) or shared != sources():
            raise SystemExit("Sources changed during compilation; rerun after edits finish.")
        log = (work / "main.log").read_text(encoding="utf-8", errors="replace")
        if "There were undefined references" in log or "There were undefined citations" in log:
            raise SystemExit("Compilation left undefined references or citations.")
        for name in ("main.pdf", "main.bbl", "main.log"):
            if not (work / name).is_file():
                raise SystemExit(f"Missing compiler output: {name}")
            shutil.copyfile(work / name, build / name)
        (build / "compiler-output.log").write_text("\n".join(run_log), encoding="utf-8")
    shutil.copyfile(build / "main.pdf", pdf)
    version = subprocess.run([executable, "--version" if engine != "latexmk" else "-version"], text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True).stdout.splitlines()[0]
    report = {"schema_version": 1, "edition": args.edition, "engine": engine, "compiler_version": version,
              "source_sha256": before, "pdf_sha256": digest(build / "main.pdf"),
              "bbl_sha256": digest(build / "main.bbl")}
    (build / "build-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if args.edition == "arxiv":
        submission_archive(source, build, before)
    warnings = [line for line in log.splitlines() if "Overfull" in line or "Warning:" in line]
    print(f"PASS: {pdf.relative_to(ROOT)}; bibliography and build report in {build.relative_to(ROOT)}/")
    if args.edition == "arxiv":
        print("PASS: ignored .local/arxiv/arxiv-source.tar.gz; members verified after export.")
    for warning in warnings:
        print(warning)


if __name__ == "__main__":
    main()
