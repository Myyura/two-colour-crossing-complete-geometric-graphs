#!/usr/bin/env python3
"""Build and recheck every source, audit axiom outputs, and bind input hashes.

Uses only Python's standard library. Tools default to PATH; LEAN/LAKE or
--lean/--lake can select installed executables. No installation is performed.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from audit_sources import ROOT, audit, sha256

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_OUTPUT = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.S)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=os.environ.get("LAKE", "lake"))
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build" / "verification")
    parser.add_argument("--summary", type=Path,
                        help="Also write the portable final summary to this path")
    parser.add_argument("--original-root", type=Path)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    result = {"schema_version": 1, "status": "RUNNING",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "command": "python3 verify.py", "commands": [],
              "allowed_axioms": sorted(ALLOWED_AXIOMS),
              "trust_boundary": ["Lean 4.34.1 kernel and runtime; installed compiler and hardware",
                                 "Pinned mathlib and transitive dependencies, using their existing build artifacts",
                                 "ConvexOptimum is an explicit mathematical hypothesis in the final theorem",
                                 "Source NP-hardness, machine-time, NP-membership and target-threshold bit bound are not formalized here"]}
    record = out / "summary.json"

    def save():
        record.write_text(json.dumps(result, indent=2) + "\n")

    def run(label, actual, portable):
        tick = time.monotonic()
        proc = subprocess.run(actual, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        log = out / (label + ".log")
        # Keep the public artifacts free from machine-specific paths.
        output = proc.stdout.replace(str(ROOT), "<lean-root>")
        for selected, standard in ((args.lake, "lake"), (args.lean, "lean")):
            if os.path.isabs(selected):
                output = output.replace(selected, standard)
        output = output.replace(str(ROOT.parent), "<repository-root>")
        output = output.replace(str(Path.home()), "<home>")
        log.write_text(output)
        result["commands"].append({"label": label, "argv": portable,
                                   "exit_code": proc.returncode,
                                   "elapsed_seconds": round(time.monotonic() - tick, 3),
                                   "log": log.name, "sha256": sha256(log)})
        save()
        print(f"{label}: exit {proc.returncode}", flush=True)
        if proc.returncode != 0:
            raise RuntimeError(f"{label} failed; see {log.name}")
        if "sorryAx" in output:
            raise RuntimeError(f"{label}: sorryAx appeared in compiler output")
        return output

    try:
        initial = audit(args.original_root)
        result["source_audit"] = {k: v for k, v in initial.items() if k != "axiom_queries"}
        tracked = sorted([*initial["axiom_queries"], "lakefile.toml", "lean-toolchain",
                          "lake-manifest.json", "source-manifest.json", "audit_sources.py", "verify.py"])
        before = {name: sha256(ROOT / name) for name in tracked}
        result["input_sha256"] = before
        save()
        version = run("lean-version", [args.lake, "env", args.lean, "--version"],
                      ["lake", "env", "lean", "--version"]).strip()
        expected = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
        if not re.search(r"Lean \(version " + re.escape(expected) + r"(?:,|\))", version):
            raise RuntimeError(f"installed Lean version does not match pinned {expected}")
        result["lean_version"] = version
        result["lake_version"] = run("lake-version", [args.lake, "--version"], ["lake", "--version"]).strip()
        run("build-Q4", [args.lake, "build", "Q4"], ["lake", "build", "Q4"])
        axioms, query_count, warnings = {}, 0, []
        sources = sorted(name for name in initial["axiom_queries"] if name != "Q4.lean") + ["Q4.lean"]
        for number, source in enumerate(sources, 1):
            label = f"source-{number:03d}-" + source[:-5].replace("/", "-")
            output = run(label, [args.lake, "env", args.lean, source], ["lake", "env", "lean", source])
            observed = AXIOM_OUTPUT.findall(output)
            expected_queries = initial["axiom_queries"][source]
            if len(observed) != len(expected_queries):
                raise RuntimeError(f"axiom-output count mismatch: {source}: {len(observed)} != {len(expected_queries)}")
            for (name, raw), query in zip(observed, expected_queries):
                if name != query and not name.endswith("." + query):
                    raise RuntimeError(f"axiom query resolved unexpectedly: {source}: {query} -> {name}")
                used = {item.strip() for item in raw.split(",") if item.strip()}
                if not used <= ALLOWED_AXIOMS:
                    raise RuntimeError(f"nonstandard axiom dependencies: {name}: {sorted(used)}")
                if name in axioms and axioms[name] != sorted(used):
                    raise RuntimeError(f"inconsistent axiom outputs: {name}")
                axioms[name] = sorted(used)
            query_count += len(expected_queries)
            warnings.extend(line for line in output.splitlines() if ": warning:" in line)
        final = audit(args.original_root)
        after = {name: sha256(ROOT / name) for name in tracked}
        if before != after or initial != final:
            raise RuntimeError("source, configuration, manifest or verifier changed during verification")
        theorem = "Q4.Candidate.ConstructedReduction.constructed_maxcut_instance"
        if theorem not in axioms:
            raise RuntimeError("final theorem axiom audit is missing")
        result.update(status="PASS", full_build_passed=True, per_file_rechecks=len(sources),
                      all_source_and_configuration_hashes_unchanged=True,
                      axiom_query_count=query_count, distinct_declarations_audited=len(axioms),
                      axiom_dependencies=dict(sorted(axioms.items())),
                      final_theorem=theorem, final_theorem_axioms=axioms[theorem],
                      warning_lines=sorted(set(warnings)))
    except Exception as error:
        result.update(status="FAIL", error=str(error).replace(str(ROOT), "<lean-root>"))
    result["elapsed_seconds"] = round(time.monotonic() - started, 3)
    result["finished_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    if args.summary:
        args.summary.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("status", "elapsed_seconds")}), flush=True)
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
