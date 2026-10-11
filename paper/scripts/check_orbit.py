#!/usr/bin/env python3
"""
Exact checks of the identity and the forced orbit (Lemmas 5.1 and 5.2):

  theta_i = (ell g^{s-1-i} + a g^i) / g^s,
  g theta_i - theta_{i+1} = (g^2 - 1) ell / g^{i+2}            (Lemma 5.1),
  theta_{i+1} = g theta_i - D_i (mod 1),  D_i = ell' / g^{i+2} mod 1,
  ell' = (g^2 - 1) ell mod g^s                                   (Lemma 5.2),

in exact rational arithmetic: exhaustively over all (ell, a, i) for small
(g, s), and at random (ell, a) for larger ones.

Usage:  python3 check_orbit.py
"""
import random
from fractions import Fraction as Fr


def theta(g, s, ell, a, i):
    return Fr(ell * g ** (s - 1 - i) + a * g ** i, g ** s)


def check(g, s, pairs):
    bad = 0
    for ell, a in pairs:
        lp = ((g * g - 1) * ell) % g ** s
        for i in range(s - 1):
            t0, t1 = theta(g, s, ell, a, i), theta(g, s, ell, a, i + 1)
            if g * t0 - t1 != Fr((g * g - 1) * ell, g ** (i + 2)):
                bad += 1
            D = Fr(lp % g ** (i + 2), g ** (i + 2))
            if (g * t0 - D - t1) % 1 != 0:
                bad += 1
    return bad


if __name__ == "__main__":
    for g, s in ((2, 8), (3, 5), (4, 4), (5, 3), (10, 3)):
        N = g ** s
        pairs = [(ell, a) for ell in range(N) for a in range(N)]
        print("exhaustive g=%d s=%d: %d pairs, violations %d" % (g, s, len(pairs), check(g, s, pairs)))
    random.seed(1)
    for g, s in ((2, 16), (3, 10), (10, 6), (12, 5), (16, 5)):
        N = g ** s
        pairs = [(random.randrange(N), random.randrange(N)) for _ in range(2000)]
        print("random     g=%d s=%d: %d pairs, violations %d" % (g, s, len(pairs), check(g, s, pairs)))
