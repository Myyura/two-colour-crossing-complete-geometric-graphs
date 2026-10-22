#!/usr/bin/env python3
"""Check the public file manifest and export public repository/source archives."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "release-manifest.json"
EPOCH = 1792627200  # 2026-10-22 00:00 UTC; archive timestamps, not a publication date.


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def private_exclusions() -> list[str]:
    """Optional local-only privacy checks; excluded values never enter the artifact."""
    path = ROOT / ".local" / "publication-exclusions.json"
    if not path.is_file():
        return []
    values = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(values, list) or any(not isinstance(v, str) or not v for v in values):
        raise ValueError("Local publication exclusions must be a list of nonempty strings.")
    return values


def git_files() -> list[str] | None:
    if not (ROOT / ".git").exists():
        return None
    ignored_tracked = subprocess.run(
        ["git", "ls-files", "--cached", "--ignored", "--exclude-standard", "-z"],
        cwd=ROOT, stdout=subprocess.PIPE, check=True).stdout
    if ignored_tracked:
        raise ValueError("Tracked files violate the publication allowlist: "
                         + ", ".join(ignored_tracked.decode("utf-8").rstrip("\0").split("\0")))
    result = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
                            cwd=ROOT, stdout=subprocess.PIPE, check=True)
    return sorted(set(result.stdout.decode("utf-8").rstrip("\0").split("\0")) - {"", MANIFEST.name})


def inspect(relative: str) -> dict[str, object]:
    parts = PurePosixPath(relative)
    if parts.is_absolute() or ".." in parts.parts or ".git" in parts.parts:
        raise ValueError(f"Invalid release path: {relative}")
    path = ROOT / relative
    if any(p.is_symlink() for p in (path, *path.parents) if p != ROOT.parent):
        raise ValueError(f"Symlinks cannot enter the release: {relative}")
    if not path.is_file():
        raise ValueError(f"Missing release file: {relative}")
    data = path.read_bytes()
    # Check content, including the compressed verification transcript.
    checked = gzip.decompress(data) if relative.endswith(".log.gz") else data
    for value in private_exclusions():
        if value.casefold() in relative.casefold():
            raise ValueError(f"Private identity found in release filename: {relative}")
        if any(value.casefold().encode(encoding).lower() in checked.lower() for encoding in ("utf-8", "utf-16-be")):
            raise ValueError(f"Private identity found in {relative}; the excluded value is not printed.")
    if path.suffix not in {".pdf"}:
        for prefix in (b"/" + b"Users/", b"/usr/" + b"local/google/"):
            if prefix in checked:
                raise ValueError(f"Personal absolute path found in {relative}")
    return {"path": relative, "bytes": len(data), "sha256": digest(data)}


def check() -> dict:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    names = [entry["path"] for entry in manifest["files"]]
    if names != sorted(set(names)):
        raise ValueError("Manifest paths must be sorted and unique.")
    actual = [inspect(name) for name in names]
    if actual != manifest["files"]:
        changed = [a["path"] for a, b in zip(actual, manifest["files"]) if a != b]
        raise ValueError("Manifest hash/size mismatch: " + ", ".join(changed))
    selected = git_files()
    if selected is not None and selected != names:
        raise ValueError(f"Git selection differs from manifest: {sorted(set(selected) ^ set(names))}")
    total = sum(item["bytes"] for item in actual)
    print(f"PASS: {len(actual)} public files plus release-manifest.json; {total:,} bytes before compression.")
    return manifest


def refresh() -> None:
    names = git_files()
    if names is None:
        raise ValueError("Refreshing requires the curated Git checkout; an exported archive can only be checked.")
    manifest = {"schema_version": 1,
                "description": "Public artifact only; intermediate exploration is excluded by the root allowlist.",
                "files": [inspect(name) for name in names]}
    MANIFEST.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    check()


def export() -> None:
    manifest = check()
    destination = ROOT / ".local" / "build" / "releases"
    destination.mkdir(parents=True, exist_ok=True)
    public = {entry["path"]: (ROOT / entry["path"]).read_bytes() for entry in manifest["files"]}
    public[MANIFEST.name] = MANIFEST.read_bytes()
    tex_prefix = "paper/tex/"
    tex = {name.removeprefix(tex_prefix): data for name, data in public.items() if name.startswith(tex_prefix)}
    report = json.loads((ROOT / ".local/build/paper/build-report.json").read_text(encoding="utf-8"))
    if report.get("edition") != "public":
        raise ValueError("Public export requires a current public-edition build report.")
    if report["source_sha256"] != {name: digest(data) for name, data in tex.items()}:
        raise ValueError("Paper changed since compilation. Run tools/build_paper.py again.")
    bbl = (ROOT / ".local/build/paper/main.bbl").read_bytes()
    if digest(bbl) != report["bbl_sha256"] or digest(public["paper/manuscript.pdf"]) != report["pdf_sha256"]:
        raise ValueError("Paper PDF/bibliography no longer matches the verified compilation.")
    tex["main.bbl"] = bbl
    # Validate both archive inputs before replacing either existing archive.
    github = destination / "github.zip"
    with zipfile.ZipFile(github, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(public.items()):
            info = zipfile.ZipInfo("two-colour-crossing/" + name, (2026, 10, 22, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    with zipfile.ZipFile(github) as archive:
        restored = {name.removeprefix("two-colour-crossing/"): archive.read(name) for name in archive.namelist()}
    if restored != public:
        raise ValueError("GitHub archive round-trip mismatch.")

    # This archive uses public metadata. Local submission files are never read here.
    source_archive = destination / "public-source.tar.gz"
    with source_archive.open("wb") as output, gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=EPOCH) as compressed:
        with tarfile.open(fileobj=compressed, mode="w") as archive:
            for name, data in sorted(tex.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, EPOCH
                archive.addfile(info, io.BytesIO(data))
    with tarfile.open(source_archive, "r:gz") as archive:
        restored_tex = {entry.name: archive.extractfile(entry).read() for entry in archive.getmembers()}
    if restored_tex != tex:
        raise ValueError("Public source archive round-trip mismatch.")
    report = {"schema_version": 1, "archives": [
        {"path": path.name, "bytes": path.stat().st_size, "sha256": digest(path.read_bytes())}
        for path in (github, source_archive)], "github_file_count": len(public), "public_source_file_count": len(tex)}
    (destination / "archive-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: .local/build/releases/github.zip and .local/build/releases/public-source.tar.gz; both byte-verified after export.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["refresh", "check", "export"])
    args = parser.parse_args()
    try:
        {"refresh": refresh, "check": check, "export": export}[args.command]()
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
