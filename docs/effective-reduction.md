# Effective construction and binary complexity

This supplement supplies the deterministic algorithm and binary-complexity argument that accompany the [formal threshold theorem](formalization.md). The Lean theorem proves existence, correctness, and explicit point and coordinate bounds. The argument below connects its construction interfaces to a polynomial-time many-one reduction in the usual bit model.

## Input and parameters

The source input is an explicit permutation \(\pi\in S_n\), \(n\ge1\), and a binary integer \(k\). Its inversion graph has \(m\) edges, and its minimum number of monochromatic edges is \(g(\pi)=m-\operatorname{MaxCut}(\pi)\). Let \(t=m-k\), with subtraction in the integers.

Use

\[
\begin{gathered}
q=2^{20}(n+1),\quad S=nq,\quad H=2^{20000}(S+1)^{40},\\
W=H^4,\quad B=H^5,\quad D=512SW,\quad O=514SW,\\
T=2^{13}O^2,\quad A=2^{26}(S+1)O^2,\quad\Delta=q^2H^{16}.
\end{gathered}
\]

Here \(T\) and \(A\) are the numeric increment and amplitude used in the program recipe; the edge-class letter \(T\) elsewhere denotes the frame–program edges. The number of program points is \(P\), and \(N=O+B+P\).

## Deterministic construction

1. **Compute the base and prototypes.** Evaluate the explicit rational expressions in [GlobalGeometryScales](../lean/Q4/Candidate/GlobalGeometryScales.lean), [OriginalVertexLayout](../lean/Q4/Candidate/OriginalVertexLayout.lean), and [ProgramGeometry](../lean/Q4/Candidate/ProgramGeometry.lean). All crossing tests use exact orientation determinants.
2. **Compute the catalogue.** Evaluate the finite prototype response tables. Ordinary multiplicities use rational ceilings; rank multiplicities use the cumulative greedy recurrence in [RankCorrection](../lean/Q4/Candidate/RankCorrection.lean). Cache each cumulative value. Enumerate labels in family, macro, gap, and copy order. These counts depend on the base and prototypes, before any final perturbation.
3. **Compute one common radius.** In [OrientationPreservation](../lean/Q4/Candidate/OrientationPreservation.lean), `constructionRadius` is the minimum of \(1/4\), a positive cap margin divided by eight, a positive height margin, and a nonzero base–base–prototype determinant margin divided by `8 * baseBudget`. The finite margin sets include the value one to handle empty sets. The positivity theorem ensures that the computed radius \(\delta\) is positive. The determinant list has \(O(N^3)\) entries.
4. **Insert all program copies.** Set \(a=N^2+N+2\). For each label, scan its fixed \(a\times a\) rational grid in lexicographic order and choose the first candidate distinct from all previous points and lying on no line through two previous points. Every candidate is already in the permitted cap and height region. `fixed_grid_extension` guarantees a surviving point at each step.
5. **Compute the baseline and output threshold.** Evaluate the rational expression \(K_0\) below on this actual placement and output the point coordinates together with \(K=\lfloor K_0+\Delta(m-k)+\Delta/4\rfloor\).

This procedure is deterministic. It does not solve the source problem or optimize the target graph. Some Lean definitions use classical choice for convenient finite indexing or existence statements. The algorithm need not execute those choices: `placed_maxcut_threshold` holds for **every** placement satisfying the proved conditions, so the explicit lexicographic choice is covered. Enumerating the finite labels also avoids any need to compute a particular abstract `Fintype.equivFin`.

## Operation count and intermediate sizes

At most \(N\) points are inserted. Each insertion examines at most \(a^2=O(N^4)\) candidates. Each candidate requires at most \(O(N^2)\) equality and orientation tests against previous points and their pairwise lines. Thus placement uses at most \(O(N^7)\) exact rational operations.

The counting guarantee is uniform: at most \(N^2\) previous ordered point pairs define forbidden lines, each containing at most \(a\) grid candidates; occupied points exclude at most another \(N\) candidates. The choice \(a=N^2+N+2\) leaves a strict surplus of candidates. No unbounded search or progressively shrinking radius is used.

The base, prototype, response-table, and catalogue calculations have polynomially many indices bounded by powers of \(N\). The greedy recurrence is evaluated iteratively. A direct evaluation of the baseline costs at most \(O(N^6)\) table operations after caching the frozen fan colours, and is dominated by the placement bound.

The actual catalogue theorem gives

\[
P\le2^{80}(S+1)^4H^3.
\]

The coordinate and size theorems then give

\[
N\le3H^5,
\qquad L\le2^{17}H^{10},
\qquad H\le2^{20840}(n+1)^{80}.
\]

Every coordinate has a representation with numerator and nonzero denominator of absolute value at most \(2^L\). The total coordinate encoding length is therefore \(O(N(L+1))\), a fixed polynomial in \(n\). These are degree-400 and degree-800 bounds for \(N\) and \(L\), respectively, with large absolute constants.

Intermediate bit lengths are polynomial as well. The prototype expressions have fixed degree. A finite rational sum can be computed with a denominator whose bit length is bounded by the sum of the input denominator lengths. A finite minimum selects an existing value. Each new point is computed directly from its prototype, the same \(\delta\), and the fixed grid parameters. The insertion does not multiply the denominator by a new radius at every step. Orientation tests involve only a constant number of additions and multiplications of these bounded-size rationals. Exact comparison, integer arithmetic, and gcd reduction therefore implement the operation bound in polynomial bit time.

## The computable baseline

On the actual placed coordinates, define

\[
K_0=
\operatorname{ComputedBackground.background}(Z(B))
+\operatorname{ComputedCore.baseFloor}+Z(D).
\]

The arguments suppressed in this display are the original and frame coordinates, actual program points, site labels, and computed frozen fan colours. They are the same arguments used in the final threshold theorem.

The [background formula](../lean/Q4/Candidate/ComputedBackground.lean) evaluates the canonical grid, adds the negative parts of all canonical single-edge flip differences, includes the actual frozen fan–fan contribution, and adds \(Z(B)\). The [core formula](../lean/Q4/Candidate/ComputedCore.lean) evaluates palette–palette and palette–fan terms and adds the smaller of the two explicit unary costs for every other core edge. The final term is \(Z(D)\).

These are finite arithmetic expressions. The minimum of two known unary values is evaluated separately for each edge. No unknown source optimum, core optimum, grid optimum, or instance-dependent global background optimum occurs in the formula. The cast lemmas identify these rational expressions with the real-valued quantities used in the inequalities.

## An explicit threshold bound

Let \(G=BO\), \(F=BP\), and \(C=\binom O2\). Each is at most \(N^2\), and each atomic crossing cost is zero or one.

| Component | Sufficient absolute bound |
|---|---:|
| Canonical grid plus its negative single-flip corrections | \(2N^6\) |
| Frozen fan–fan cost | \(N^4/2\) |
| Each of \(Z(B),Z(D)\) | \(N^4/4\) |
| Core palette cost plus all unary minima | \(7N^4/2\) |

For example, a grid value has at most \(GF+G^2\le2N^4\) atoms; the absolute single-flip difference is at most \(2N^4\). There are at most \(N^2\) such differences. The core palette terms have at most \(C^2/2+CF\) atoms, and each free unary has at most \(C+F\) atoms. These counts yield the conservative bound

\[
|K_0|\le16N^6.
\]

The denominators in these cost expressions come only from explicit division by two or four; coordinate denominators enter crossing predicates, not the zero-or-one cost values. Since \(q,H\le N\) and \(m\le N^2\),

\[
\Delta\le N^{18},
\]

and the floor changes a number by less than one. Consequently,

\[
\begin{aligned}
|K|
&\le16N^6+N^{18}(N^2+|k|)+N^{18}/4+1\\
&\le32N^{20}(|k|+1).
\end{aligned}
\]

Thus the threshold has \(O(\log N+\log(|k|+1))\) bits, with the usual constant allowance for zero and the sign. This includes the bit length of an arbitrarily large source threshold. The threshold bound is a mathematical supplement; it is not a separately formalized Lean theorem.

## Both directions and NP membership

The full-drawing estimate is

\[
K_0+\Delta g(\pi)-E_-
\le\operatorname{OPT}(P)
\le K_0+\Delta g(\pi)+E_+,
\quad E_-,E_+\ge0,
\quad2^{18}(E_-+E_+)<\Delta.
\]

If \(g(\pi)\le t\), its upper bound is below \(K_0+\Delta t+\Delta/4\). If \(g(\pi)>t\), integrality gives \(g(\pi)\ge t+1\), and its lower bound is above the same real threshold. Since the target cost is an integer, taking the floor preserves the decision equivalence. This uses the conservative local cost \(2SW^4\) and the supported error window, rather than requiring an earlier draft's tighter constants.

All colours in the complete graph are free. The edge bijection and `decision_transport` in [CompleteInput](../lean/Q4/Candidate/CompleteInput.lean) carry the internal objective to the standard complete graph on these exact coordinates in both directions. Optimizers used to prove inequalities are mathematical witnesses, not subroutines of the construction.

A target certificate contains \(\binom N2\) colour bits. Check distinctness and general position using \(O(N^3)\) exact orientation tests. For every disjoint edge pair \(ab,cd\), proper crossing is equivalent to

\[
\operatorname{orient}(a,b,c)\operatorname{orient}(a,b,d)<0,
\qquad
\operatorname{orient}(c,d,a)\operatorname{orient}(c,d,b)<0.
\]

There are \(O(N^4)\) edge pairs to test and count. All arithmetic has polynomial bit cost, proving membership in NP. Counting crossing pairs permits several pairs to share an intersection location.

For an empty source, decide \(0\ge k\) directly and output a fixed YES or NO instance. A fixed YES instance is two distinct integer points at threshold zero. A fixed NO instance is the five points \((i,i^2)\), \(0\le i<5\), at threshold zero. If nonnegative target thresholds are required, use that NO instance whenever the computed \(K<0\); do not truncate \(K\) to zero. Finally, clearing all rational denominators by one positive common scale preserves the crossing relation and has polynomial binary cost, giving the integer-coordinate restriction.

Together with the [two external results](theorem.md#the-two-external-results), these facts establish the stated NP-completeness result. The construction is specified and proved effective; this repository does not claim an extracted implementation or an experimental generation of its full asymptotic instances.
