# Two-colour crossing minimization in complete geometric graphs is NP-hard

**Myyura** · **The Kai Project** · [中文说明](README.zh-CN.md)

This repository contains a proof of NP-completeness for the decision version of two-colour crossing minimization in a fixed complete geometric graph, together with Lean proofs and reproducible finite diagnostics.

The input consists of distinct rational points with no three collinear, encoded in binary, and an integer threshold. Every edge of the straight-line complete graph may independently receive either colour. The objective counts unordered pairs of properly crossing edges of the same colour. The result also holds for integer coordinates; exact minimization is NP-hard.

**Project:** [GitHub repository](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs) · [CI runs](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs/actions/workflows/verify.yml). The manuscript has not yet been submitted to arXiv. The verification record below describes the original local run; current CI results are available through the CI link.

## Read the proof

| Resource | Contents |
|---|---|
| [Manuscript](paper/manuscript.pdf) · [LaTeX source](paper/tex/main.tex) | Mathematical proof and references. |
| [Theorem and scope](docs/theorem.md) | Exact input, quantifiers, reduction, and external results. |
| [Proof guide](docs/proof-guide.md) | Argument structure and corresponding Lean modules. |
| [Effective reduction](docs/effective-reduction.md) | Deterministic construction, binary complexity, and computable threshold. |
| [Formalization](docs/formalization.md) · [Lean instructions](lean/README.md) | Final declaration, verification procedure, and trust boundary. |
| [Verification summary](audit/README.md) · [Provenance](docs/provenance.md) | What was checked and how the manuscript and formal proof relate. |
| [Finite diagnostics](computations/README.md) | Exact finite checks and their limited scope. |

The reduction outputs one complete graph instance. Its proof includes all completion edges and cross-class costs. The conservative estimates used in the formal assembly are a local bound of `2SW^4` and the strict gap `2^18(E_- + E_+) < Δ`.

## What Lean verifies

The final declaration is

```text
Q4.Candidate.ConstructedReduction.constructed_maxcut_instance
```

It constructs the same rational point set for the all-edge threshold equivalence, injectivity, general position, and polynomial point/coordinate bounds. Its explicit external certificate is

```text
∀ m, ConvexOptimum m (knownZ m)
```

This is supplied by the known two-page complete-graph optimum theorem. Represented permutation-graph MaxCut supplies the source hardness. Both results are precisely cited in [theorem.md](docs/theorem.md#the-two-external-results).

The recorded local run built and individually rechecked **128 Lean source files**, using **Lean 4.34.1** and the pinned mathlib dependencies. It matched **883 axiom queries covering 882 distinct declarations**; their reported dependencies were limited to `propext`, `Classical.choice`, and `Quot.sound`. See the [machine-readable record](lean/verification-summary.json). These are counts of checked sources and selected queries, not a claim that each declaration was separately audited.

Machine-time complexity, NP membership, source NP-hardness, the external convex optimum, and the separate threshold bit bound are not reproved as Lean complexity-class theorems. The written effective-reduction argument supplies the `O(N^7)` exact-operation construction, polynomial intermediate bit lengths, and `|K| ≤ 32N^20(|k| + 1)`. The verification trusts the Lean runtime and kernel and pinned dependency artifacts; it does not rebuild all of mathlib from source.

## Repository layout

The public files keep their normal layout: `paper/` contains the manuscript, `lean/` the proof package, `computations/` the finite checks, `docs/` the exposition, and `audit/` the retained verification record. Local material is consolidated under the ignored `.local/` directory:

| Directory | Local contents |
|---|---|
| `.local/arxiv/` | Optional submission metadata and its generated source, PDF and archive. |
| `.local/research/` | Earlier research notes, scripts, results, source material and the historical Lean workspace, with their relative layout preserved. |
| `.local/build/` | Build products, dependency caches, fresh verification logs and export archives. |

In the maintained local workspace, `lean/.lake` and `lean/build` are ignored compatibility symlinks into `.local/build/lean/`, so the usual Lean commands still work. The local material and symlinks are excluded from the public source package.

## Reproduce and package

To check the recorded release, run these commands from the repository root with Python 3.10 or later:

```bash
python3 tools/repository.py check
python3 computations/run_checks.py
python3 lean/verify.py
```

The first command checks the public package and manifests. The finite diagnostics use only Python's standard library. Lean verification additionally needs elan and the pinned toolchain/dependencies; follow the [Lean setup instructions](lean/README.md). Its default output is available through `lean/build/verification/`; in the maintained local workspace, the compatibility symlink stores it under `.local/build/lean/`. The published verification summary is preserved.

Maintainers rebuilding the paper should use a Git checkout. First run:

```bash
python3 tools/build_paper.py
```

This needs a supported LaTeX engine (`latexmk`, `pdflatex`, or `tectonic`). Inspect the regenerated [PDF](paper/manuscript.pdf) before intentionally updating the release record:

```bash
python3 tools/repository.py refresh
python3 tools/repository.py export
```

Rebuilding can change PDF metadata and therefore its hash. `refresh` deliberately records the reviewed public files and requires a Git checkout; it is not part of checking the original release. The export command verifies the recorded files and their compilation binding, then writes `github.zip` and `public-source.tar.gz` under `.local/build/releases/`. It does not upload or submit them.

An optional local submission edition can use separate metadata from the ignored `.local/arxiv/metadata.json`. Running `python3 tools/build_paper.py --edition arxiv` keeps that edition's source, PDF and submission archive under the ignored `.local/arxiv/` directory; those files are excluded from public exports.

The [CI workflow](.github/workflows/verify.yml) runs package and finite checks in one job and Lean verification in another. The latter prepares the environment with the [official Lean Action](https://github.com/leanprover/lean-action) and runs the repository's full verifier. It uses the official mathlib cache and disables reuse of GitHub project caches. Live results are listed in [GitHub Actions](https://github.com/Myyura/two-colour-crossing-complete-geometric-graphs/actions/workflows/verify.yml); the successful verification recorded above is the original local run.

## Attribution and licenses

Author: **Myyura**; affiliation: **The Kai Project**. Citation metadata is in [CITATION.cff](CITATION.cff). Code, including the Lean development and verification scripts, is licensed under **Apache-2.0**. The paper and accompanying paper documentation are licensed under **CC BY 4.0**. See the [license notice](LICENSE) for the boundaries and full license texts.

The work was prepared with AI assistance and includes separate LLM review sessions. Those reviews are not external human peer review. Finite diagnostic success is not a replacement for the universal proof or the stated formalization boundary.
