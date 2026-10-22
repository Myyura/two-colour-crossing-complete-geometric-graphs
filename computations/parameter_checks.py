"""Exact finite checks of the conservative parameter/error budget.

Universal parameter bounds are proved in Lean. This program evaluates five
explicit source sizes and some standalone rational coefficient inequalities.
"""
from fractions import Fraction
import json


def run():
    assert 2*83*220**3 < 2**31
    assert 2*105*106 < 2**15
    assert 2**290+2*2**307+2**182 < 2**310
    assert Fraction(9, 2)+Fraction(8, 514)+Fraction(10, 1024) < 5
    assert Fraction(8, 514)+Fraction(8, 1024)+Fraction(1, 2) < 1
    rows = []
    for n in [1, 2, 5, 10, 100]:
        q = 2**20*(n+1)
        S = n*q
        d = S+1
        H = 2**20000*d**40
        W, B = H**4, H**5
        o = 514*S*W
        delta = q*q*W**4
        error_bound = 2**310*d**14*H**15 + 10*B*S*W**2 + 2*S*W**4
        assert B > o and B % 8 == 0
        assert 2**85*d**4*2**4096 <= H
        assert 2**18*error_bound < delta
        rows.append({"n": n, "H_bits": H.bit_length(),
                     "conservative_error_less_than_Delta_over_2pow18": True})
    return {"cases": rows, "rational_coefficient_checks": 5,
            "scope": "Five source sizes; all-n statements are Lean theorems."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
