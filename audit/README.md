# Verification and review record

The public Lean package was rebuilt and individually rechecked on 22 October 2026 with Lean 4.34.1. All **128 source files passed**: 127 unchanged modules in the final theorem's dependency closure and one explicit aggregate entry point. The verification took 390.112 seconds. The [machine-readable summary](../lean/verification-summary.json) records 131 command results, source and configuration hashes, 883 axiom queries covering 882 distinct declarations, and five nonfatal linter warnings.

The queried dependencies, including those of the final theorem, contain only `propext`, `Classical.choice`, and `Quot.sound`. The source audit rejects proof placeholders, custom axioms, and the unsafe escape mechanisms listed in [the verifier](../lean/audit_sources.py). This does not mean that every declaration was individually queried, or that the external mathematics was re-proved.

## Reproduction and retained logs

Follow [the Lean instructions](../lean/README.md), then run from the repository root:

```sh
python3 tools/repository.py check
python3 computations/run_checks.py
python3 lean/verify.py
```

The manifest check validates the recorded release bytes. By default, `lean/verify.py` writes new logs and a summary through the ignored `lean/build/verification/` path, preserving the published record. In the maintained local workspace, `lean/build` and `lean/.lake` are compatibility symlinks into `.local/build/lean/`, where verification outputs and dependency caches are stored. A new run can differ in platform, timings, and logs. Only an explicit `--summary` option aimed at the published summary replaces it; a maintainer can refresh the release manifest after reviewing an intentional update.

The [compressed transcript](lean-verification.log.gz) contains the public package's 131 command logs in order, with each log's name and SHA-256. These are the verifier's portable logs: local machine paths were replaced by `<lean-root>` and `<home>` before the per-log hashes were recorded. Packaging checked every individual log against the summary before concatenation. The [history record](verification-history.json) records the transcript hash and distinguishes the earlier 173-source workspace replay from the smaller public package.

Both Lean runs reused pinned external dependency caches; neither rebuilt all of mathlib. The trusted boundary includes the Lean kernel/runtime, pinned dependency artifacts, and the host execution environment. The current source package can be rechecked without the earlier research workspace.

## Mathematical scope

The final theorem is `Q4.Candidate.ConstructedReduction.constructed_maxcut_instance`. It concerns one legal complete geometric graph and one integer threshold, with all edges freely two-coloured and the required equivalence to the represented permutation-graph cut threshold.

Its explicit external premise is the known convex complete-graph optimum formula, supplied mathematically by the cited two-page crossing-number theorem. Source NP-hardness, the deterministic machine-time analysis, NP membership, and the separate threshold bit bound are natural-language arguments. See the [formalization boundary](../docs/formalization.md) and the manuscript's formalization section.

The four [exact computational suites](../computations/README.md) also passed. They check finite geometry, counting, parameter samples, and a six-point completion counterexample. They neither materialize the asymptotic reduction nor optimize its full target instances.

## Manuscript review

The [new manuscript review](new-manuscript-review.md) records a separate LLM review of the rewritten exposition and its correspondence to the formal statements. It is distinct from kernel verification and is not human journal peer review. The [provenance statement](../docs/provenance.md) explains the earlier review process and why incorrect aggregate-review claims were not carried into the public article.

There is no claim here of a probability of correctness, acceptance by a journal, an arXiv endorsement, or a successful remote CI run. These records describe the checks actually performed on the local release.

## Manuscript build and package checks

The public edition was rebuilt after the metadata update. It is 33 pages, with Myyura as the PDF author and The Kai Project displayed as the affiliation. The revised cover was rendered and visually inspected; all font programs are embedded, text is extractable on every page, and no unresolved reference or overfull box was found. Pages 2–33 have exactly the same extracted text as the previously reviewed and fully rendered manuscript. The module-name table produces nonfatal underfull-box diagnostics and was checked for legibility. These layout checks are separate from the mathematical review.

The source archive from that build was extracted into a separate directory and compiled without the research workspace. It produced the same 33 pages and exactly the same extracted page text. The GitHub archive was also extracted separately; its public manifest and all 128 Lean source hashes/imports passed the standalone checks. The recorded check resolved all 143 relative documentation links and all 103 TeX references. These counts describe that verification run, rather than an unperformed check of later metadata or documentation revisions.

Updating the author and affiliation metadata changes `main.tex`, the separate `metadata.tex` file, and the compiled PDF bytes without changing the reviewed mathematical sections. Current source and PDF bindings are recorded in [verification-history.json](verification-history.json) and the release manifest. No Lean proof or finite-check program was changed for this metadata revision, so the recorded mathematical verification remains bound to the same sources.

The public export writes `github.zip` and `public-source.tar.gz` under `.local/build/releases/`. It verifies every stored member byte against its input and excludes Git history, dependency caches, reference drafts, exploratory directories and the optional local submission edition. Local submission files remain under `.local/arxiv/`, research history under `.local/research/`, and build products under `.local/build/`. The whole `.local/` directory is ignored and excluded from the public package.
