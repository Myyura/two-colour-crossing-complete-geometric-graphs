# Independent review of the rewritten manuscript

Date: 2026-10-22.

Status: **PASS within the stated scope of this independent LLM-assisted
mathematical review.** All chapters and their final revisions listed below have
been read; no unresolved substantive mathematical issue was identified. This
status is a review result, not a substitute for mathematical proof or human peer
review, and applies to the mathematical source versions recorded below.

The reviewer did not write the new manuscript chapters or the underlying Lean
proofs. The reviewer prepared the public Lean dependency closure and verification
scripts, so verification-packaging claims are not an independent audit of that
reviewer's own software. The mathematical review below is an independent
LLM-assisted reading of the new prose against the actual definitions and final
Lean statement. It is not human peer review, and a successful Lean build is not
treated as proof that a differently worded manuscript statement is correct.

## Material examined

- `paper/tex/sections/introduction.tex`, `formalization.tex`, and `completion.tex`.
- The complete continuous/discrete stability and probe-freezing chapter.
- The complete source-core and final decision-reduction chapters.
- The complete geometry chapter, including the revised explicit common scales,
  determinant estimates, finite perturbation radius and deterministic grid search.
- `paper/tex/main.tex` and `references.bib`.
- Relevant retained Lean declarations, including `ConstructedReduction`,
  `CandidateSize`, `ConvexBackground`, `GlobalGeometryScales`, `MacroLayout`,
  `OrdinaryNonincident`, and the actual rank and original-vertex definitions.
- The external-theorem and effective-construction scope, checked against the
  local primary-source PDFs: Ábrego et al., Theorem 7 (PDF page 11), and the
  permutation-graph MaxCut paper, Theorem 1 (PDF page 2) and its explicit
  permutation-model construction in Section 4 (PDF page 8). The source
  NP-completeness theorem is used as an external result, not reproved here.

No old exploratory branch was reclassified, and no Lean proof source was edited
or recompiled for this manuscript review.

## Checked mathematical interfaces

**Problem, complexity and encoding.** The problem has fixed rational coordinates,
general position, the full unweighted complete graph and free colours on every
edge. Proper crossing pairs, including pairs sharing a geometric intersection
location, are counted separately. The NP certificate has one bit per edge; exact
orientation tests and legality checks have polynomial bit complexity. Clearing
all denominators by one positive product preserves every orientation sign and
has polynomial output bit length. The represented permutation-graph MaxCut
source is used only for its decision threshold, not for a stronger optimal
extension claim. The convex two-page result supplies the explicitly stated
`ConvexOptimum` hypothesis, including its lower bound and attainment parts.

**Formalization statement.** The final theorem quantifies over every `n ≥ 1`,
permutation and integer source threshold, and uses one common coordinate
witness for injectivity, general position, the rational numerator/denominator
budget and the free complete-edge threshold equivalence. The manuscript's
`3 Hhat^5` point bound and `2^17 Hhat^10` coordinate certificate exponent match
the actual declaration. The prose distinguishes these statements from source
NP-hardness, machine-time, NP membership and the separately proved target
threshold bit bound.

**Continuous stability.** The alternation-deficit identity has the correct
factor eight. The positive/negative triple argument proves the claimed threshold
approximation. The comparison-energy decomposition has nonnegative slice
deficits. The distributional mixed-derivative identity, interior box estimate,
diagonal Poincaré estimate and rounding do not require an unproved measurable
selection or a positive lower bound on diagonal lengths. The two half-threshold
variance argument, mean correction and all displayed exponent/constant estimates
give the stated two-phase result, including zero excess.

**Finite grid and freezing.** Cell discrepancies, canonical field estimates and
the bootstrap give the stated bound for every actual minimizer. The degree
estimate is applied only to strip vertices; corner vertices enter through their
cardinality, avoiding an invalid small-degree assertion. The exact simultaneous
flip correction gives the lower bound for an arbitrary localized support and
arbitrary unary costs. The prescribed-phase upper witness is explicit. Probe
freezing keeps the same grid and counts probe–probe neighbours in the outside
degree, so sequential recolouring does not omit their costs. The later lower
bound correctly uses localized support rather than claiming the frozen grid is
still a conditional minimizer.

**Geometric realization and bit complexity.** The revised macro mesh, including
`-1/4 + v/(2(D_m+1))` for dummy vertices, matches the actual Lean formulas. With
`eta` the capped minimum positive macro separation, the manuscript uses
`mu = eta^2/(10000(W+1))` and `tau = mu eta^2/(1000(B+1))`. The common-scale
inequalities, ordinary parent and nonparent ray tests, rank endpoint gap and
support-line displacement estimates were checked by expansion. In particular,
the ordinary parent determinant margin dominates its clone perturbation; rank
steering is bounded by `tau/50`; and the nonincident support tests retain strict
sign margins under the stated constants. Both endpoint tests needed for proper
crossings are accounted for. The double-chain cap and the right-cap separation
justify the exclusions involving nonfans and same-chain edges.

The finite radius uses the actual prototype set and the minima for orientation,
cap and height margins. Each coordinate moves by less than half that radius,
which preserves the strict height bound as well as the signed tests. The grid
size `m = N^2 + N + 2` gives more candidate points than all existing forbidden
lines and used points can exclude. A single radius is computed from rational
prototype data before placement, avoiding recursive denominator growth. The
resulting polynomial operation count and bit-length argument therefore cover
the actual deterministic construction. Tests that were zero at a prototype are
not silently treated as preserved signs; the required noncrossings use a
strict same-side endpoint or ray test.

**Core and source.** Successive uniformization of independent source classes is
nonincreasing and leaves earlier classes uniform. The late negative-prefix rank
correction retains its initial constant. Palette forcing is claimed only inside
the frozen core optimization, and its single-flip comparison includes arbitrary
remaining core colours. The dummy contribution is colour-independent except for
its known convex internal optimum. Deleting the enumerated local constraints
leaves independent short-edge unaries and the intended source blowup; restoring
them costs at most `2 S W^4`. One compatible core colouring supplies the upper
bound. The baseline contains only explicit counts and two-value unary minima.

**Complete graph and final threshold.** The argument starts with the graph with
the `Y` class deleted, includes fan–fan costs in the common background, and pays
for every deleted constraint through `R_Y`. Its lower and upper constructions
use the same final drawing. The parameter exponents and numerical error budget
give `2^18 (E_- + E_+) < Delta`. Source integrality, the quarter-signal margin
and the floor give both decision directions for arbitrary integer thresholds.
The negative-threshold branch is handled correctly rather than clipped to zero.
The stated polynomial threshold-bit bound is safely looser than the finite
counting estimates.

**Completion appendix.** The two proposed colourings were checked independently
with exact integer determinants. Their monochromatic crossing lists are exactly
`(02,15),(03,14),(24,35)` and `(02,13),(04,35),(14,25)`, respectively. The six
convex five-point subsets give the lower bound three by double counting. The
conditional added-edge contributions two and three therefore follow without
assuming an unproved optimum certificate.

## Findings and disposition

1. The initial aggregate TeX file omitted the completion appendix despite two
   references to it. The final `main.tex` includes it after `\appendix`.
   **Closed after read-back.**
2. In the slice-error estimate, a strict inequality with both sides zero at
   `epsilon = 0` was replaced by a non-strict inequality. This was a boundary-case
   wording error, not a failure of the positive-scale argument.
   **Closed after read-back.**
3. The first realization text used successive dyadic choices and a dummy mesh
   different from the exact Lean coordinates. The final revision uses the actual
   `macroSpacing`, `programScale` and `cloneScale` formulas and the actual dummy
   mesh. Its quantitative interface estimates and finite-radius argument have
   been independently read and checked. **Closed.**
4. The initial chapters used `N` for both target points and comparison-grid
   vertices. The integrated chapters now use `N` for target points and `N_g`
   for comparison-grid vertices, with the separate local grid notation declared
   in the stability chapter. **Closed after read-back.**

No unresolved substantive mathematical error was identified. A source-level
label/reference/citation scan found no duplicate labels, undefined references
or undefined citations. PDF compilation and visual layout review are separate
checks performed by the root task; they are not inferred from this mathematical
review.

The external convex optimum theorem and represented permutation-graph MaxCut
NP-completeness theorem remain explicit mathematical trust boundaries. The
manuscript's polynomial-time implementation, NP membership, threshold encoding
and integer-coordinate scaling are prose proofs; the final Lean theorem does
not by itself formalize machine complexity classes. This review does not
upgrade those claims to Lean-checked statements.

## Reviewed source versions

The mathematical sections and bibliography retain the reviewed SHA-256 hashes below. The public edition subsequently changed the author and affiliation metadata in `main.tex` to Myyura and The Kai Project. This metadata-only revision changes the aggregate source hash, without extending the mathematical review to new mathematics. The current `main.tex` bytes are bound by the release manifest; the earlier aggregate-file hash is not presented as the current public version.

| File | SHA-256 |
| --- | --- |
| `paper/tex/sections/completion.tex` | `acae2c4e74fd02a82d09c641bcd6cc3a01fd53357bed570e12e01135e4147a86` |
| `paper/tex/sections/core.tex` | `0175a7f0bb37b04e5d5f1fb410c1afaf945fce3d40d2cf578e04c7fe859376cb` |
| `paper/tex/sections/formalization.tex` | `80eda14f3f90fe3e5ff137c971584529a4dcf522baa8a1bb6134224c3be09cb8` |
| `paper/tex/sections/geometry.tex` | `1d4ede30f6563e889dc451881d874fe32c398bd86fb55072a428069c8d46b74f` |
| `paper/tex/sections/introduction.tex` | `43ceb2877738462f6bbb95a3e9749e3969b7b74fb0d8979944453950198b876d` |
| `paper/tex/sections/reduction.tex` | `df6094467495996206bd6f73bb5167ad36d950d8c52fe50a7b0dbbec048eca59` |
| `paper/tex/sections/stability.tex` | `78610f0684c115aa057223fb55d5715b3c3bc427fe05d620ae990a3ad4aaa26e` |
| `paper/tex/references.bib` | `f2bd9f8733c83f9cd04def388a453719ba3a4781bc3a293d19faaee8860bfc7e` |

Public metadata revision (22 October 2026): only the author/affiliation rendering and PDF author metadata changed. The mathematical sections and bibliography still match the hashes above. Source hashes at that metadata revision:

- `paper/tex/main.tex`: `4892ab669f37e9eda6b725545d73125604d1c9585e753c00a794b194a1c9d78f`.
- `paper/tex/metadata.tex`: `ed01eb9df3ac70ad87fe9f8e115f1485329eaf01e4826da85f93512b94e26111`.

## Title revision (22 October 2026)

The title now reads **Two-colour crossing minimization in complete geometric graphs is NP-hard**. This wording describes the optimization problem; the abstract and theorem continue to state NP-completeness of its threshold decision version. Only the displayed title and PDF title metadata in `main.tex` changed in this revision. The abstract, mathematical chapters, bibliography and author metadata are unchanged. This editorial change does not extend the mathematical review above.

Current `paper/tex/main.tex` SHA-256: `bf5f9e1ee182c1a0e937d5fd17b7e2d9e02826dec642f33d70699bf3ab183ca5`.
