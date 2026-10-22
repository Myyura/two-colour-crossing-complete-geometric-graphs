"""Exhaustive six-point completion obstruction; exact arithmetic only."""
from fractions import Fraction
from itertools import combinations
import json


def cross(e, f, points):
    # Solve a+t(b-a)=c+u(d-c), independently of the determinant sign oracle.
    if set(e) & set(f):
        return False
    a, b = (points[i] for i in e)
    c, d = (points[i] for i in f)
    v = (b[0]-a[0], b[1]-a[1])
    w = (d[0]-c[0], d[1]-c[1])
    determinant = v[1]*w[0]-v[0]*w[1]
    if determinant == 0:
        return False
    rhs = (c[0]-a[0], c[1]-a[1])
    t = Fraction(-rhs[0]*w[1]+rhs[1]*w[0], determinant)
    u = Fraction(v[0]*rhs[1]-v[1]*rhs[0], determinant)
    return 0 < t < 1 and 0 < u < 1


def run():
    points = [(i, i*i) for i in range(6)]
    edges = list(combinations(range(6), 2))
    pairs = [(i, j) for i, j in combinations(range(len(edges)), 2)
             if cross(edges[i], edges[j], points)]
    first, second = edges.index((2, 4)), edges.index((3, 5))
    best = {True: len(pairs), False: len(pairs)}
    witnesses = {}
    # Fix the last edge to zero: every colouring has a representative by
    # globally swapping the two colours. Both imposed relations are invariant.
    for mask in range(1 << (len(edges)-1)):
        colours = [(mask >> i) & 1 for i in range(len(edges)-1)] + [0]
        cost = sum(colours[i] == colours[j] for i, j in pairs)
        equal = colours[first] == colours[second]
        if cost < best[equal]:
            best[equal] = cost
            witnesses[equal] = colours
    assert len(pairs) == 15 and best == {True: 3, False: 3}
    return {"points": points, "edges": edges, "proper_crossing_pairs": len(pairs),
            "colouring_representatives": 1 << 14,
            "minimum_source_same": best[True], "minimum_source_different": best[False],
            "minimum_extra_same": best[True]-1,
            "minimum_extra_different": best[False],
            "witness_same": witnesses[True], "witness_different": witnesses[False],
            "scope": "Exhaustive fixed K6; not a growing-family hardness proof."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
