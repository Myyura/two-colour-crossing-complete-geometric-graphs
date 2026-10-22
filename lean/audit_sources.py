#!/usr/bin/env python3
"""Audit the exact local import closure and immutable source manifest."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by)\b")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source):
    """Mask nested Lean comments and strings, preserving line numbers."""
    output, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                output.extend("  ")
                i += 2
                continue
            output.append("\n" if char == "\n" else " ")
            i += 1
            continue
        if string:
            if char == "\\":
                output.extend("  ")
                i += 2
                continue
            if char == '"':
                string = False
            output.append("\n" if char == "\n" else " ")
            i += 1
            continue
        if pair == "/-":
            depth = 1
            output.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            output.extend(" " * (end - i))
            i = end
        elif char == '"':
            string = True
            output.append(" ")
            i += 1
        else:
            output.append(char)
            i += 1
    if depth or string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(output)


def imports(code):
    result = []
    for line in code.splitlines():
        if re.match(r"^\s*(?:public\s+)?import\b", line):
            match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_.]+)\s*", line)
            if not match:
                raise ValueError(f"unsupported import syntax: {line}")
            result.append(match.group(1))
    return result


def queries(code):
    return re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", code, re.M)


def audit(original_root=None):
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    entries = manifest["modules"]
    names = [entry["module"] for entry in entries]
    if len(names) != len(set(names)):
        raise ValueError("duplicate module in source manifest")
    expected = {entry["path"] for entry in entries} | {"Q4.lean"}
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*.lean")
              if not any(part in {".lake", "build"} for part in p.relative_to(ROOT).parts)}
    if expected != actual:
        raise ValueError(f"source-set mismatch: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}")
    codes = {path: code_only((ROOT / path).read_text()) for path in sorted(expected)}
    for path, code in codes.items():
        match = FORBIDDEN.search(code)
        if match:
            raise ValueError(f"forbidden token {match.group()} in {path}:{code[:match.start()].count(chr(10))+1}")
    root_imports = imports(codes["Q4.lean"])
    if root_imports != sorted(names):
        raise ValueError("Q4.lean must explicitly import every closure module exactly once in sorted order")
    by_name = {entry["module"]: entry for entry in entries}
    external, visited = set(), set()

    def visit(name):
        if name in visited:
            return
        if name not in by_name:
            if name == "Q4" or name.startswith("Q4."):
                raise ValueError(f"missing project dependency: {name}")
            external.add(name)
            return
        visited.add(name)
        entry = by_name[name]
        observed = imports(codes[entry["path"]])
        if observed != entry["imports"]:
            raise ValueError(f"import list changed for {name}")
        for dependency in observed:
            visit(dependency)

    visit(manifest["entry_module"])
    if visited != set(names):
        raise ValueError(f"manifest includes modules outside the entry closure: {sorted(set(names)-visited)}")
    if sorted(external) != manifest["external_imports"]:
        raise ValueError("external import set changed")
    for entry in entries + manifest["generated_and_configuration"]:
        path = ROOT / entry["path"]
        if sha256(path) != entry["sha256"]:
            raise ValueError(f"manifest hash mismatch: {entry['path']}")
        if original_root is not None and "original_path" in entry:
            original = original_root / entry["original_path"]
            if sha256(original) != entry["sha256"]:
                raise ValueError(f"original source differs: {entry['original_path']}")
    return {
        "status": "PASS", "entry_module": manifest["entry_module"],
        "source_count": len(expected), "closure_module_count": len(names),
        "candidate_module_count": sum(name.startswith("Q4.Candidate.") for name in names),
        "other_modules": sorted(name for name in names if not name.startswith("Q4.Candidate.")),
        "exact_source_set": True, "explicit_root_coverage": True,
        "exact_transitive_local_import_closure": True,
        "forbidden_proof_tokens": [], "manifest_hashes_match": True,
        "original_sources_compared": original_root is not None,
        "axiom_queries": {path: queries(code) for path, code in codes.items()},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original-root", type=Path,
                        help="Optional historical q4_lean directory; never needed for a public checkout")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(args.original_root)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload)
    print(payload, end="")
