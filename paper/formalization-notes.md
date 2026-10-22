# Manuscript and formalization versions

Date: 22 October 2026. This note concerns the newly authored [manuscript source](tex/main.tex), its [PDF](manuscript.pdf), and the final Lean theorem described in the [formalization scope](../docs/formalization.md).

## Constants used in the new manuscript

| Item | Earlier reference draft | New manuscript and final formalization |
| --- | --- | --- |
| Local crossing contribution | At most `2 S W^4 / 3` | The conservative bound `2 S W^4`, with a complete counting proof. The sharper earlier bound is not claimed to have been formalized. |
| Aggregate error window | `E_minus + E_plus < Delta / 2^19` | `2^18 * (E_minus + E_plus) < Delta`. This weaker estimate is sufficient for the quarter-signal threshold. |
| Selected-edge unary budget | `10 B S W^2` | The actual selected-edge total is at most `8 S H^13`, hence at most the stated budget `10 B S W^2 = 10 S H^13`. |
| Canonical phase | Strict `u + v < 1` | The same strict convention, including midpoint ties. |
| Geometric scales | Successive small-parameter choices | The explicit Lean scales `mu = eta^2 / (10000 (W+1))` and `tau = mu eta^2 / (1000 (B+1))`, with quantitative sign margins and fixed rational insertion grids. |
| Encoding and threshold | Informal polynomial construction | A deterministic algorithm and explicit bit arguments accompany Lean's legal rational instance and two-way integer-threshold equivalence. |

Here `eta` is the minimum of one and all nonzero distances between the early/late macro parameters and dummy parameters; it does not include frame spacing. The new manuscript also uses the formal construction's dummy parameters `-1/4 + v/(2(D_m+1))`. All program multiplicities are chosen after their prototype tables and responses are fixed.

The scale choice is `q = 2^20 (n+1)`, `S = nq`, `d = S+1`, `H = 2^20000 d^40`, `W = H^4`, `B = H^5`, and `o = 514 S W`. The point count is bounded by a fixed polynomial of degree 400 in the source size. The constants are enormous; no practical full-size target instance was generated or optimized.

An earlier reference draft informed the research. The public source is a separate, newly authored manuscript; the earlier status paragraphs and diagnostic counts are not inherited as current claims. The current public source and PDF are identified by the release manifest.

## Formalization boundary

`Q4.Candidate.ConstructedReduction.constructed_maxcut_instance` relates represented permutation-graph MaxCut to a **single** fixed straight-line drawing of a complete unweighted graph. All target edges remain free to take either colour. The same rational coordinates satisfy injectivity, general position, encoding bounds, and the two-way threshold equivalence.

The theorem explicitly takes the known convex complete-graph optimum formula as a mathematical parameter. That literature result and the source NP-hardness theorem were not reproved in Lean. The project does not define machine complexity classes or prove a machine-time bound in Lean. The complete complexity conclusion combines the formalized new mathematics, the cited external theorems, and the written effective-construction proof, including NP membership, common-denominator integer coordinates and the separate threshold bit bound. See the [theorem statement](../docs/theorem.md), [proof guide](../docs/proof-guide.md), and [effective reduction](../docs/effective-reduction.md).

The public verification checked 128 source files: 127 unchanged dependency modules and one explicit aggregate entry point. Its designated axiom queries have dependencies only on `propext`, `Classical.choice`, and `Quot.sound`. The earlier full-workspace check covered 173 files; that historical count must not be confused with the public package. Both checks reused pinned external dependency caches and did not rebuild all of mathlib. Exact commands, counts and trust boundaries are in the [verification record](../audit/README.md).

## Audit corrections

The [audit overview](../audit/README.md) distinguishes mathematical proof, finite Python diagnostics, Lean verification, and LLM-assisted review. Incorrect claims in an earlier third-party aggregate report were not carried into the new manuscript: these included `Theta(n^42)`, substituted scale formulas, `min(B,o)=B`, a uniform `floor(-gamma/B)` rank correction, and `y_R-a_s<0`. The actual rank correction uses gap-dependent weights and a cumulative greedy construction; the actual geometry has `a_s < y_L < y_R < b_t`.

LLM-assisted reviews are not human journal peer review. Neither review outcomes nor finite diagnostics establish a numerical correctness probability or journal acceptance. The public preprint is attributed to **Myyura**, **The Kai Project**, and licensed **CC BY 4.0**, as instructed by the author.
