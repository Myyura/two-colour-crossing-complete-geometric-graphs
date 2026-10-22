# The theorem and its scope

The decision version of two-colour crossing minimization for a fixed complete geometric graph is NP-complete. Computing its exact minimum is NP-hard. The reduction is a deterministic polynomial-time many-one reduction from MaxCut on permutation graphs supplied with a permutation representation.

The [manuscript](../paper/manuscript.pdf), the [effective-reduction supplement](effective-reduction.md), and the [Lean development](formalization.md) give the argument. They use the conservative error bounds described below. The [verification summary](../audit/README.md) records the checks and their limits.

## Problem definition

An input is an ordered list of distinct points

\[
P=(p_0,\ldots,p_{N-1})\in(\mathbb Q^2)^N
\]

with no three collinear, and an integer threshold \(K\). Rational coordinates and the threshold are encoded in binary. Every unordered pair of points is an edge of the fixed straight-line drawing of \(K_N\). There are no edge weights, missing edges, or prescribed colours.

A colouring is an arbitrary function

\[
\chi:\binom{[N]}2\longrightarrow\{0,1\}.
\]

Let \(\mathcal X(P)\) be the set of unordered pairs of edges whose relative interiors cross properly. Define

\[
M(P,\chi)=\sum_{\{e,f\}\in\mathcal X(P)}
  \mathbf 1[\chi(e)=\chi(f)],
\qquad
\operatorname{OPT}(P)=\min_\chi M(P,\chi).
\]

Shared endpoints do not count. If several edge pairs cross at one geometric point, each pair contributes separately. Thus the general-position assumption here is **no three vertices collinear**; it does not require every crossing location to be distinct. The decision question is whether \(\operatorname{OPT}(P)\le K\). Invalid coordinate encodings or point sets can be rejected in polynomial time.

**Theorem.** This decision problem is NP-complete, including its restriction to integer-coordinate inputs. Its exact optimization version is NP-hard.

The integer-coordinate conclusion follows by multiplying all coordinates by the positive product of their denominators. This preserves every orientation sign and crossing pair and increases the total binary encoding length by only a polynomial factor. Negative thresholds are immediate NO instances; if the chosen input convention requires \(K\ge0\), the reduction replaces a negative output threshold by a fixed NO instance.

## Source and reduction statement

For a permutation \(\pi\in S_n\), let

\[
E_\pi=\{\{i,j\}:i<j,\ \pi(i)>\pi(j)\},
\quad m=|E_\pi|,
\quad g(\pi)=m-\operatorname{MaxCut}(E_\pi).
\]

For every \(n\ge1\), \(\pi\), and binary integer \(k\), the construction outputs one point set \(P\) and one integer \(K\) such that

\[
\exists\chi\;M(P,\chi)\le K
\quad\Longleftrightarrow\quad
\exists\psi:[n]\to\{0,1\}\;
  |\{\{i,j\}\in E_\pi:\psi(i)\ne\psi(j)\}|\ge k.
\]

All target edge colours are free in both directions. The palette and frozen fan colours used in the proof are derived within the optimality analysis; they are not additional input constraints.

Write

\[
F(n)=2^{20840}(n+1)^{80}.
\]

The same constructed coordinates satisfy

\[
N\le3F(n)^5,
\qquad
L\le2^{17}F(n)^{10},
\]

where each coordinate has an integer numerator and a nonzero integer denominator with absolute value at most \(2^L\). Its ordinary binary length is therefore at most \(L+1\), plus a sign bit, for each numerator or denominator. The coordinate witnesses, injectivity, general position, and threshold equivalence concern **one and the same point set**.

The effective construction uses at most \(O(N^7)\) exact rational operations, with polynomial intermediate bit lengths. Its threshold satisfies

\[
|K|\le32N^{20}(|k|+1).
\]

The constants and polynomial degrees are large. The result establishes complexity; it does not provide a practical reduction for computational experiments.

## The two external results

1. **Source hardness.** Celina M. H. de Figueiredo, Alexsander A. de Melo, Fabiano S. Oliveira, and Ana Silva, *MaxCut on permutation graphs is NP-complete*, Journal of Graph Theory 104 (2023), 5–16, DOI [10.1002/jgt.22948](https://doi.org/10.1002/jgt.22948). Theorem 1 is on printed page 6; Section 4 explicitly constructs a two-permutation representation. Relabelling the first permutation yields the inversion-graph model above. Only its decision-threshold hardness is used. [Author-hosted paper](https://www.cos.ufrj.br/~celina/ftp/j/jgt.22948.pdf).
2. **Convex background value.** Bernardo M. Ábrego, Oswin Aichholzer, Silvia Fernández-Merchant, Pedro Ramos, and Gelasio Salazar, *The 2-page crossing number of \(K_n\)*, Theorem 7, page 11 of the [arXiv PDF](https://arxiv.org/pdf/1206.5669). It gives the two-page complete-graph optimum

   \[
   Z(r)=\frac14
   \left\lfloor\frac r2\right\rfloor
   \left\lfloor\frac{r-1}2\right\rfloor
   \left\lfloor\frac{r-2}2\right\rfloor
   \left\lfloor\frac{r-3}2\right\rfloor.
   \]

   The endpoint-alternation correspondence supplies the optimum for two-colouring the chords of a convex complete graph. Set \(Z(0)=Z(1)=Z(2)=0\). This result supplies the frame and dummy values; it places no convexity restriction on the full target instance.

These source statements were checked against the linked papers on 22 October 2026. Neither external theorem is reproved in Lean here.

## Mathematical proof and formal proof

The final Lean declaration is

```text
Q4.Candidate.ConstructedReduction.constructed_maxcut_instance
```

It proves the legal rational instance, explicit point and coordinate bounds, and full threshold equivalence. Its explicit mathematical certificate parameter is

```text
∀ m, ConvexOptimum m (knownZ m)
```

which is supplied by the second external result. This certificate includes a lower bound for all chord colourings and an attaining colouring. It is a theorem hypothesis, not a custom axiom.

The complexity conclusion also uses the source hardness theorem, the deterministic construction and bit-complexity argument, and NP membership. The development does not define NP or a machine model, prove the external hardness theorem, or formalize the separate bound on the threshold's binary length. See [formalization](formalization.md) for the precise boundary.

The error analysis used by the formal development allows a local contribution of \(2SW^4\), and proves

\[
2^{18}(E_-+E_+)<\Delta.
\]

These bounds replace an earlier draft's tighter \(2SW^4/3\) local estimate and \(2^{-19}\Delta\) aggregate window. Both the lower and upper comparisons use the same computable baseline and the same \(\Delta/4\) threshold offset. [Proof guide](proof-guide.md).
