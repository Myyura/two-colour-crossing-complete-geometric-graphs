# Lean verification

This project contains the exact local transitive import closure of
`Q4.Candidate.ConstructedReduction`: 123 Candidate modules and four foundational
modules (`Counting`, `CleanWire`, `SimultaneousFlip`, and `JointProbe`). The 127
original module files are copied byte-for-byte. The new `Q4.lean` explicitly
imports all of them, giving 128 checked sources in total. The other 45 historical
modules are excluded; they are not required by any retained import.

`CleanWire` is still required by the integer-to-rational crossing conversion in
`ConvexSeparation`; `JointProbe` is used by complete-class energy accounting and
imports `SimultaneousFlip`, which imports `Counting`. Keeping entire original
modules preserves their exact proof bytes, including any older helper statements
contained in those four files. This is a minimal **module** closure, not a claim
that every declaration is individually needed by the final theorem.

## Run

The toolchain is Lean 4.34.1. `lake-manifest.json` pins mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612` and fixes its transitive dependencies.
With elan and Python 3 installed, initialize the pinned dependencies and their
official build cache from this directory:

```sh
lake exe cache get
python3 verify.py
```

`lake update` is unnecessary and may change the lock file. The verifier itself
does not install tools or request a dependency update. A fresh dependency setup
may need network access through Lake; a populated dependency cache works offline.

From the repository root the same verification is `python3 lean/verify.py`.
The executable names default to `lake` and `lean` on `PATH`; set `LAKE`/`LEAN` or
pass `--lake`/`--lean` to select installed alternatives. Python uses only its
standard library. No user-specific path is required.

The default machine-readable result is `build/verification/summary.json`, with
one log per command in that directory, with paths here relative to `lean/`.
In the maintained local workspace, `lean/build` and `lean/.lake` are ignored
compatibility symlinks into `.local/build/lean/`, so generated results and
dependency caches remain under `.local/`. The commands above remain
unchanged, and neither the local files nor these links are shipped in the
public source package. `--output-dir PATH` changes the run directory;
`--summary PATH` also saves the final JSON elsewhere. The committed
`verification-summary.json` records the preparation run and is not overwritten
by the default command.

For a source-only check, run `python3 audit_sources.py`. The optional
`--original-root PATH` checks copied bytes against a historical Lean directory.
In the maintained local workspace this is `.local/research/q4_lean/`, relative
to the repository root. That directory is not needed by a public checkout.

## What is checked

1. The actual source set equals the manifest, and the root explicitly imports
   every retained module exactly once.
2. Recomputing the final module's local import closure gives exactly the retained
   set. Source/configuration hashes match `source-manifest.json`.
3. A comment/string-aware scan rejects proof holes, custom axiom declarations,
   `native_decide`, and unsafe/implementation-replacement declarations.
4. The pinned Lean version is checked, `lake build Q4` succeeds, and every one of
   the 128 sources is re-elaborated separately with `lake env lean`.
5. Each retained `#print axioms` query is matched to its actual compiler output.
   All dependencies must be among `propext`, `Classical.choice`, and `Quot.sound`.
   Existing per-module queries and historical root-only queries are retained.
   This audits selected key declarations, not every declaration individually.
6. All source, configuration, manifest, and verifier hashes are unchanged after
   the run; the source set and closure are checked again.

`source-manifest.json` records original module paths relative to the historical
project, SHA256 digests, every direct import, and the excluded-module list. Those
historical paths are provenance data, not dependencies of this checkout.

## Scope and trust

The final declaration is
`Q4.Candidate.ConstructedReduction.constructed_maxcut_instance`. It constructs one
complete rational drawing with injective coordinates, general position,
polynomial point/coordinate budgets, and the exact free-edge integer-threshold
equivalence to represented permutation-graph MaxCut.

The known convex complete-graph optimum is an **explicit hypothesis**
`∀ m, ConvexOptimum m (knownZ m)`, not a custom axiom declaration. Its external
mathematical proof must still be supplied when interpreting the result. Source
NP-hardness, machine-time complexity, NP membership, and the separate target
threshold bit bound are covered by the accompanying mathematical argument, not
formalized as complexity-class theorems here.

Verification trusts the Lean kernel/runtime, the installed toolchain and machine,
and the pinned mathlib/dependency build artifacts. It does not independently
rebuild or audit all of mathlib. No unchecked native-decision proof is introduced
by the retained local sources. A successful run certifies these exact Lean
statements and their declared hypotheses; it is not a substitute for reviewing
their correspondence with the paper.
