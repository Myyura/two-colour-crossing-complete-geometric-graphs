"""Run the public, exact finite checks; Python standard library only."""
import argparse
import hashlib
from itertools import permutations
import json
from pathlib import Path
import time
import appendix_completion
import core_combinatorics
import parameter_checks
import program_geometry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, help="Write a new result record instead of comparing the reference record.")
    args = parser.parse_args()
    started = time.monotonic()
    root = Path(__file__).resolve().parent
    results = {
        "appendix_completion": appendix_completion.run(),
        "core_combinatorics": [core_combinatorics.run(p) for p in permutations(range(3))],
        "program_geometry": [program_geometry.run(2,3,8,3,[1,0]),
                             program_geometry.run(2,4,16,4,[0,1])],
        "parameter_checks": parameter_checks.run(),
    }
    record = {"scope": "Exact finite diagnostics only; not a full reduction instance or universal proof.",
              "script_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sorted(root.glob("*.py"))},
              "results": results}
    # JSON normalization turns tuples into lists consistently.
    record = json.loads(json.dumps(record))
    if args.record:
        args.record.parent.mkdir(parents=True, exist_ok=True)
        args.record.write_text(json.dumps(record, indent=2) + "\n")
    else:
        expected = json.loads((root / "expected-results.json").read_text())
        if record != expected:
            raise SystemExit("FAIL: finite checks or source hashes differ from expected-results.json")
    print(json.dumps({"status": "PASS", "suites": 4,
                      "elapsed_seconds": round(time.monotonic()-started, 3)}))


if __name__ == "__main__":
    main()
