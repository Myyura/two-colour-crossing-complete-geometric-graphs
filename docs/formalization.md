# Lean formalization

The Lean development proves the new mathematical construction through its final complete-graph threshold theorem. It uses Lean 4.34.1 and mathlib at revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). The [toolchain file](../lean/lean-toolchain) and [dependency manifest](../lean/lake-manifest.json) pin the environment.

The public source tree is [lean/](../lean/). Its retained module names include `Q4.Candidate`; this is a stable namespace, not a claim that every informal statement in the earlier manuscript has been formalized verbatim. The [proof guide](proof-guide.md) maps the mathematical obligations to modules.

## Final declaration

The entry theorem is in [ConstructedReduction.lean](../lean/Q4/Candidate/ConstructedReduction.lean):

```lean
Q4.Candidate.ConstructedReduction.constructed_maxcut_instance
```

Its inputs are \(n\ge1\), `pi : Equiv.Perm (Fin n)`, an arbitrary integer source threshold, and

```lean
hconvex : ∀ m, ConvexOptimum m (knownZ m)
```

Its conclusion produces one `N`, one coordinate function `Fin N → Point`, and one integer threshold. On these same coordinates it proves:

- injectivity and absence of collinear triples;
- the stated polynomial point bound;
- binary numerator/denominator certificates for every rational coordinate;
- equivalence between a colouring of **all** standard complete-graph edges with at most the target number of monochromatic proper-crossing pairs and a source cut of at least the source threshold.

The final declaration does not assume a program placement, palette precolouring, catalogue bound, source optimum, geometric realization, error gap, or unknown background optimum. Those ingredients are constructed or proved in its dependencies. It obtains its placement once and uses it for the energy, geometry, encoding, and threshold.

## Meaning of the external certificate

[ConvexBackground](../lean/Q4/Candidate/ConvexBackground.lean) defines `ConvexOptimum m z` as a minimum witness for the all-chord monochromatic alternation objective: a lower bound for every colouring and an attaining colouring. The externally supplied value is the explicit rational formula `knownZ m`.

The [known two-page theorem](theorem.md#the-two-external-results) supplies this certificate through endpoint alternation. The formal development proves its transfer to the actual frame and dummy geometry. It does not reprove the literature theorem. The certificate is an explicit proposition argument; the source files do not introduce it as a custom axiom.

The source MaxCut NP-completeness theorem is used outside Lean to infer hardness from the threshold equivalence. Thus there are two external mathematical results in the complete complexity argument, but only the convex optimum appears as a parameter of this final Lean theorem.

## Definition and quantifier checks

| Interface | What it means |
|---|---|
| `CompleteDrawing.Inner N` | Every unordered vertex pair, represented once with increasing endpoints. |
| `ConvexSeparation.ProperCross` | Two strict opposite-side orientation tests on rational coordinates. |
| `CompleteInput.plainPairs` | Actual crossing edge pairs, counted once each. |
| `CompleteInput.edgeEquiv` | Bijection from all internal endpoint classes to the standard complete edge set. |
| `CompleteInput.energy_transport` | Equality of internal and standard complete-graph objectives. |
| `CompleteInput.decision_transport` | Both existential directions over all unrestricted edge colourings. |
| `SourceSelectedEdges.sourcePairs` | The source permutation's inversion edges, not its complement. |
| `SourceCutBridge.permutation_threshold` | Integer equivalence between minimum monochromatic source edges and a MaxCut threshold. |

The internal five edge classes include all six endpoint types. In particular, original–program and program–program edges are both included in class `Y`. The target counts pairs of properly crossing edges rather than distinct geometric crossing locations.

## Verification and trust boundary

Use the [public verification instructions](../lean/README.md) and [verification script](../lean/verify.py). The explicit source manifest is checked against the source tree; the aggregate entry point imports the retained modules. Verification scans for proof holes and custom axioms, builds the project, rechecks the listed files, and reports theorem axiom dependencies. A default build alone is not the documented coverage check.

The preserved full-workspace verification checked 173 source files, including 123 `Candidate` modules. A later replay rebuilt those 173 project modules from a source-only copy without reusing project `.olean` files, and rechecked every file successfully. That historical count describes the larger workspace. The public package retains the final theorem's dependency closure and a public aggregate entry point; its own source manifest and verification records determine the public count and checks. See the [verification summary](../audit/README.md) for the packaged replay status.

The recorded theorem dependencies were limited to the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, `sorryAx`, or custom axiom was accepted in the checked project sources. This is a statement about the checked proof dependencies, not a claim that hypotheses of theorems disappear. In particular, `hconvex` remains an explicit hypothesis.

The source-only replay reused the installed, pinned external dependency caches. It did not independently rebuild all of mathlib or audit the compiler binaries. The normal trust boundary includes Lean's kernel and implementation, its standard foundations, and imported library results and artifacts. Source scans and axiom listings complement semantic review; they do not by themselves establish that a theorem expresses the intended research question.

Five distinct nonfatal linter locations occurred in the recorded development: two unused-variable notices in `AlternatingTriples`, two tactic-simplification notices in `RankGap`, and one in `ReductionGap`. They were retained in the verification record.

## What is outside the formalization

The following are part of the written complexity proof or the external literature, not Lean machine-complexity theorems in this repository:

- the NP-hardness of represented permutation-graph MaxCut;
- the known complete-graph two-page optimum;
- definitions of NP, NP-hardness, and polynomial-time many-one reductions in a machine model;
- the \(O(N^7)\) deterministic construction time and polynomial intermediate bit costs;
- the separate threshold bound \(|K|\le32N^{20}(|k|+1)\);
- the NP verifier and the common-denominator conversion to integer coordinates.

These are explained in the [theorem statement](theorem.md) and [effective-reduction supplement](effective-reduction.md). The formal theorem itself includes the rational coordinate certificates and point-count bound.

The formal error accounting uses \(2SW^4\) for local costs and \(2^{18}(E_-+E_+)<\Delta\). It does not certify an earlier draft's tighter constants. The strict \(u+v<1\) phase convention, actual program catalogue, all-edge objective, common baseline, and final threshold are connected in the checked development.

Review was AI-assisted, including separate LLM examinations of interfaces and proof components. Those reviews are not external human peer review and do not replace the proofs or kernel checks. [Provenance](provenance.md).
