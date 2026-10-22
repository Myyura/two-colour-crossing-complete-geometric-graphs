# Provenance and version scope

This repository presents the complete-geometric-graph reduction, its mathematical supplements, the Lean dependency closure, and supporting reproducibility material. The work was prepared with AI assistance. Mathematical claims, kernel verification, finite computations, and LLM reviews have different scopes and are identified separately.

## Manuscript and supported argument

The public [manuscript](../paper/manuscript.pdf), [theorem statement](theorem.md), [proof guide](proof-guide.md), [effective-reduction supplement](effective-reduction.md), and [formalization statement](formalization.md) describe the supported argument and its verification scope. The manuscript is prepared from the mathematical proof and checked formal interfaces; an earlier unpublished draft served as a reference rather than a publication-ready source.

The supported formal reduction makes these explicit choices:

| Item | Supported version |
|---|---|
| Local residual crossing cost | At most \(2SW^4\), a conservative replacement for the earlier draft's \(2SW^4/3\). |
| Aggregate error window | \(2^{18}(E_-+E_+)<\Delta\); the earlier draft's tighter window is not claimed as the formalized bound. |
| Selected unary total | \(8SH^{13}\le10SH^{13}\). |
| Canonical phase | The strict inequality \(u+v<1\), including the stated diagonal-tie convention. |
| Output baseline and threshold | Explicit rational finite sums on the actual placement, followed by an integer floor. |
| Coordinate construction | One common radius and a finite fixed-grid insertion algorithm, with explicit binary bounds. |

The conclusion uses the same decision offset \(\Delta/4\). The choices above preserve a strict separation and do not require an unproved tighter constant. The manuscript and documentation state the conservative version used in the final assembly.

## Evidence retained for readers

The [Lean source tree](../lean/) contains the modules needed for the final theorem and an explicit aggregate verification entry point. Module names are retained so that theorem names remain traceable. The published package omits unrelated exploratory branches from the proof dependency set.

The [verification summary](../audit/README.md) records source integrity, build/recheck scope, semantic review, and known limitations. The earlier full-workspace replay checked 173 source files; the public dependency-closure package has its own manifest and verification record. These two counts refer to different source sets.

The [computational checks](../computations/README.md) provide diagnostics and finite examples. A successful finite script run establishes only its documented checks. In particular, enumerating a simplified core model or testing parameter samples does not construct and independently optimize the complete asymptotic target instance. The public diagnostics use exact integer or rational arithmetic.

## Review provenance

The development and review process used LLM assistance. Different sessions reviewed mathematical sections, interfaces, geometry, and final assembly. The final interface also received a later semantic review by a session that had not authored the proof or the earlier reports. Some component-level reviewers had contributed other components; this limits any unqualified claim of complete independence.

An earlier set of five manuscript reviews used separate calls to the same model. Such calls provide distinct review attempts, not independent human referees or statistically independent error estimates. A subsequent audit identified substantive errors in their aggregate summary, including incorrect construction parameters, an invalid rank-correction formula, reversed geometric signs, and overstated verification claims. Those summary statements are not used as evidence for the theorem. The public account follows the checked source statements and formal interfaces.

The review record supports the precise report that the examined final interfaces and effective-construction argument had no remaining blocking issue identified in those checks. It does not certify a probability of correctness, publication acceptance, or completion of external human peer review. Lean verification and mathematical review remain complementary: one checks formal derivations, while the other examines definitions, external assumptions, and the match to the intended problem.

## Attribution and reuse

The public author is **Myyura**, affiliated with **The Kai Project**. Citation information is maintained in the repository's [citation metadata](../CITATION.cff). Licensing is specified by the repository's license files; this provenance note does not assign a separate license. The external papers are cited for the exact results used in [theorem.md](theorem.md#the-two-external-results), and their authorship is distinct from this repository's authorship.

Historical logs, exploratory notes, and raw review outputs are retained locally under `.local/research/`, preserving their relative directory layout; they are not part of the public proof exposition. Optional submission material is kept under `.local/arxiv/` and build products under `.local/build/`. The whole `.local/` directory is ignored and excluded from public exports. Their omission is an editorial choice to keep the published package focused. It does not turn finite evidence into a theorem or extend the formalization beyond its stated scope.
