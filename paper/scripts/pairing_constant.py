#!/usr/bin/env python3
"""
Constants from the pairing bound (Lemma 5.3 and Proposition 5.4 of the paper):

  max_a |Psi_ell(a)| <= g^s exp(-1/2 sum_i chi(Delta_i(ell))),
  chi(D) = inf{ phi(x) + phi(y) : x, y in [0, 1/2], g x + y >= D },
  phi = -log psi,  psi(eps) = sup{ f(theta) : ||theta|| >= eps },

with Delta_i(ell) >= Lambda_r(r digits of ell'), summed over ell' with a
de Bruijn transfer matrix on (r-1)-digit states.  Prints c = 1 - log_g(rho).
This is a NUMERICAL evaluation on a fine grid (not certified); the certified
constants of the paper come from window_constants.py, which is much better.

Usage:  python3 pairing_constant.py g r1,r2,...     e.g.  python3 pairing_constant.py 2 2,4,6
"""
import math
import sys

import numpy as np


def make_phi(g, M=200001):
    th = np.linspace(0, 0.5, M)
    with np.errstate(invalid='ignore', divide='ignore'):
        f = np.abs(np.sin(np.pi * g * th) / (g * np.sin(np.pi * th)))
    f[0] = 1.0
    psi = np.maximum.accumulate(f[::-1])[::-1]        # psi(eps) = max_{theta >= eps} f
    phi = -np.log(np.maximum(psi, 1e-300))
    return th, phi


def make_chi(g, th, phi, Deltas):
    out = []
    for D in Deltas:
        xs = np.linspace(0, min(D / g, 0.5), 4001)
        ys = np.clip(D - g * xs, 0, 0.5)
        ok = (g * xs + ys) >= D - 1e-15
        val = np.interp(xs, th, phi) + np.interp(ys, th, phi)
        out.append(val[ok].min() if ok.any() else np.inf)
    return np.array(out)


def pairing_c(g, r):
    th, phi = make_phi(g)
    P = g ** r
    v = np.zeros(P)
    for p in range(P):
        digs = [(p // g ** (r - 1 - j)) % g for j in range(r)]   # d_1 most significant
        v[p] = sum(d * g ** (-j - 1) for j, d in enumerate(digs))
    Lam = np.maximum(0, np.minimum(v, 1 - v - g ** (-r)))
    xi = np.exp(-make_chi(g, th, phi, Lam) / 2)
    if r == 1:
        rho = xi.sum()
    else:
        nS = g ** (r - 1)
        src = np.arange(P) // g
        dst = np.arange(P) % nS
        x = np.ones(nS)
        for _ in range(5000):
            y = np.bincount(src, weights=xi * x[dst], minlength=nS)
            y /= y.max()
            if np.max(np.abs(y - x)) < 1e-13:
                x = y
                break
            x = y
        rho = np.max(np.bincount(src, weights=xi * x[dst], minlength=nS) / x)
    return 1 - math.log(rho) / math.log(g)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(0)
    g = int(sys.argv[1])
    for r in map(int, sys.argv[2].split(',')):
        print("g=%d r=%d pairing c = %.4f" % (g, r, pairing_c(g, r)), flush=True)
