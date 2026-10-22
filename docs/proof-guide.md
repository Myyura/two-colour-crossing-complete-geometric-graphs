# Proof guide

The central obligation is to encode the source cut while accounting for **every edge of the complete target graph**. The proof supplies lower and upper bounds with a common, explicitly computable baseline. A strict gap then turns those bounds into one decision instance.

Read the [theorem statement](theorem.md) first. The [manuscript](../paper/manuscript.pdf) develops the mathematical argument. The [effective-reduction supplement](effective-reduction.md) gives the deterministic construction and encoding details used with the formal development.

## Parameters and notation

For a represented source permutation on \(n\ge1\) elements, use

\[
\begin{aligned}
q&=2^{20}(n+1), & S&=nq,\\
H&=2^{20000}(S+1)^{40}, & W&=H^4,\\
B&=H^5, & D&=512SW,\\
O&=2SW+D=514SW, & \Delta&=q^2W^4=q^2H^{16}.
\end{aligned}
\]

There are \(O\) original points, \(B\) frame points, and \(P\) program points. The total point count in these documents is always \(N=O+B+P\); the comparison grid has \(BO\) edges. The program catalogue satisfies

\[
P\le2^{80}(S+1)^4H^3,
\qquad N\le3H^5.
\]

## 1. Obtain a stable comparison grid

A double-chain arrangement makes the original–frame edges into a rectangular comparison grid. A continuous stability argument identifies two complementary phases. The finite-grid transfer controls the discrepancy between the continuum and the actual finite energy. With the permitted unary perturbations, every **minimizer** has the required localization around one phase.

The argument starts with unrestricted colourings and derives localization from optimality. It does not assume that an unknown optimum already resembles the canonical phase. Exact localization is not claimed for arbitrary approximately optimal colourings. The canonical convention is the strict inequality \(u+v<1\); diagonal ties belong to the other colour.

Main modules: [TwoPhaseStability](../lean/Q4/Candidate/TwoPhaseStability.lean), [GridStepBridge](../lean/Q4/Candidate/GridStepBridge.lean), [GridLocalization](../lean/Q4/Candidate/GridLocalization.lean).

## 2. Realize the program responses geometrically

Ordinary and rank program points have explicit rational prototypes. Their fan edges read controlled parts of the comparison grid. The proof establishes the crossing tables, field signs, nonincident-edge exclusions, and preservation under a common sufficiently small perturbation.

Rank correction uses the actual weight at each occupied internal gap and a cumulative greedy construction. A single uniform rounding formula would not provide this correction. The multiplicities and geometry are fixed before the final general-position insertion.

Main modules: [ProgramGeometry](../lean/Q4/Candidate/ProgramGeometry.lean), [ActualProgramGeometry](../lean/Q4/Candidate/ActualProgramGeometry.lean), [ActualSideGeometry](../lean/Q4/Candidate/ActualSideGeometry.lean), [RankCorrection](../lean/Q4/Candidate/RankCorrection.lean), [ActualRecipe](../lean/Q4/Candidate/ActualRecipe.lean).

## 3. Account for the complete edge set

The proof partitions all edges by endpoint type:

| Class | Endpoints |
|---|---|
| \(X\) | original–frame |
| \(T\) | frame–program |
| \(C\) | original–original |
| \(Y\) | original–program or program–program |
| \(I\) | frame–frame |

The five classes cover six endpoint types because \(Y\) combines two types. The geometric separation lemmas remove particular crossing interactions by proving that those crossings are absent. Other interactions remain in the energy. In particular, the actual fan–fan contribution is included after program points have been placed.

For the lower bound, start from a genuine optimum, identify its grid phase, and control the cost of freezing fan colours while preserving that same grid colouring. The resulting core energy is bounded below by its unrestricted minimum. Palette forcing is invoked at that core-minimum stage; palette colours need not already be forced in the original full optimum.

For the upper bound, construct one full colouring with the chosen grid phase, the frozen fan colours, and compatible core and frame choices. Terms temporarily omitted for estimates are charged when restored. Thus deleting a class during an inequality does not delete its edges from the output instance.

Main modules: [CompleteProbeFreezing](../lean/Q4/Candidate/CompleteProbeFreezing.lean), [CompleteFanFields](../lean/Q4/Candidate/CompleteFanFields.lean), [CompleteClassEnergy](../lean/Q4/Candidate/CompleteClassEnergy.lean), [CompleteBackground](../lean/Q4/Candidate/CompleteBackground.lean).

## 4. Force the palette and encode the source

The actual program catalogue makes every core minimizer agree with the palette. Selected source edges retain a bounded unary discrepancy, at most \(4B\) per edge. Dummy edges have equal unary costs in both colours. All other core edges remain part of the minimization.

Independent source replication and the bundle construction give the exact main-source minimum \(q^2W^4g(\pi)\). The extension argument chooses source, dummy, and short-edge colours in one compatible core colouring. It does not combine minima that require incompatible assignments to shared variables.

Main modules: [ActualCatalogBounds](../lean/Q4/Candidate/ActualCatalogBounds.lean), [ActualSelectedUnary](../lean/Q4/Candidate/ActualSelectedUnary.lean), [ActualDummyUnary](../lean/Q4/Candidate/ActualDummyUnary.lean), [MainSourceEncoding](../lean/Q4/Candidate/MainSourceEncoding.lean), [CoreReducedPairs](../lean/Q4/Candidate/CoreReducedPairs.lean), [CoreExtension](../lean/Q4/Candidate/CoreExtension.lean), [CoreValueBridge](../lean/Q4/Candidate/CoreValueBridge.lean).

## 5. Compute a common baseline and separate the thresholds

The common baseline is the rational number

\[
K_0=\operatorname{ComputedBackground.background}(Z(B))
  +\operatorname{ComputedCore.baseFloor}+Z(D),
\]

with the suppressed arguments all evaluated on the same actual point set. It consists of finite crossing sums, canonical single-flip differences, and a minimum of two explicit unary numbers for each relevant edge. It contains no unknown global optimum.

The full estimate is

\[
K_0+\Delta g(\pi)-E_-
\le\operatorname{OPT}(P)
\le K_0+\Delta g(\pi)+E_+,
\]

where \(E_-,E_+\ge0\) and

\[
2^{18}(E_-+E_+)<\Delta.
\]

The formal development uses the conservative local bound \(2SW^4\). Its selected-unary budget is \(8SH^{13}\le10SH^{13}\). These estimates are sufficient for the displayed gap; they do not assert an earlier draft's tighter local constant or its narrower aggregate window.

For a source threshold \(k\), put \(t=|E_\pi|-k\) and output

\[
K=\left\lfloor K_0+\Delta t+\Delta/4\right\rfloor.
\]

If \(g(\pi)\le t\), the upper estimate puts the integer target optimum at most \(K\). Otherwise the integer source optimum is at least \(t+1\), and the lower estimate puts the target optimum strictly above \(K\). Only one target instance is produced.

Main modules: [ComputedBackground](../lean/Q4/Candidate/ComputedBackground.lean), [ComputedCore](../lean/Q4/Candidate/ComputedCore.lean), [FreezingErrors](../lean/Q4/Candidate/FreezingErrors.lean), [ConservativeGap](../lean/Q4/Candidate/ConservativeGap.lean), [ActualReductionValue](../lean/Q4/Candidate/ActualReductionValue.lean), [SourceCutBridge](../lean/Q4/Candidate/SourceCutBridge.lean).

## 6. Produce one legal, finitely encoded target

A shared positive rational radius preserves the required geometric tables. A bounded fixed grid then supplies every program copy while avoiding all previously occupied points and all lines through two previous points. This gives distinct rational points with no three collinear, without a recursive shrinking procedure.

The final construction chooses this placement once. Its points determine the crossing relation, baseline, threshold, and binary coordinate certificates. The internal edge labels are transported bijectively to all unordered pairs of the resulting \(N\) vertices; both directions quantify over every colouring of those edges.

See the [effective-reduction supplement](effective-reduction.md). Main modules: [UniformInsertion](../lean/Q4/Candidate/UniformInsertion.lean), [ProgramPlacement](../lean/Q4/Candidate/ProgramPlacement.lean), [ActualCatalogParameters](../lean/Q4/Candidate/ActualCatalogParameters.lean), [CandidateSize](../lean/Q4/Candidate/CandidateSize.lean), [CompleteInput](../lean/Q4/Candidate/CompleteInput.lean), [ConstructedReduction](../lean/Q4/Candidate/ConstructedReduction.lean).
