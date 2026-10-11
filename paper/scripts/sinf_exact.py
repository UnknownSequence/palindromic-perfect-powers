#!/usr/bin/env python3
"""
Exact (floating-point) values of max_a |Psi_ell(a)| for all ell mod g^s, and
S_inf(s) = sum_{0<|ell|<g^s} max_a |Psi_ell(a)|, where

    Psi_ell(a) = sum_{m < g^s} e(-(ell rev_s(m) + a m) / g^s),

computed by one FFT (over m) for each ell.  Prints S_inf(s) and the local
growth exponent log_g(S_inf(s)/S_inf(s-1)); c_loc = 2 - exponent is the
"observed" value of c in S_inf(s) << g^{(2-c)s} (Remark 5.8 of the paper).

Usage:  python3 sinf_exact.py g s1,s2,...  [--cache]
  e.g.  python3 sinf_exact.py 2 8,9,10,11,12      (seconds)
        python3 sinf_exact.py 10 2,3,4            (about a minute)
With --cache the arrays max_a|Psi_ell| are saved as maxabs_g{g}_s{s}.npy.
Cost: g^{2s} log(g^s); memory about 16 * g^s * chunk bytes.
"""
import os
import sys
import time

import numpy as np


def rev_table(g, s):
    m = np.arange(g ** s, dtype=np.int64)
    r = np.zeros_like(m)
    t = m.copy()
    for _ in range(s):
        r = r * g + t % g
        t //= g
    return r


def maxabs(g, s, cache=False):
    """Array A with A[ell] = max_a |Psi_ell(a)| for 0 <= ell < g^s."""
    fn = "maxabs_g%d_s%d.npy" % (g, s)
    if cache and os.path.exists(fn):
        return np.load(fn)
    n = g ** s
    R = rev_table(g, s)
    chunk = max(1, min(n, (1 << 24) // n))
    out = np.empty(n)
    for l0 in range(0, n, chunk):
        ls = np.arange(l0, min(n, l0 + chunk), dtype=np.int64)
        ph = ((ls[:, None] * R[None, :]) % n).astype(float) / n
        out[ls] = np.abs(np.fft.fft(np.exp(-2j * np.pi * ph), axis=1)).max(axis=1)
    if cache:
        np.save(fn, out)
    return out


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(0)
    g = int(sys.argv[1])
    cache = "--cache" in sys.argv
    prev = None
    for s in map(int, sys.argv[2].split(',')):
        t0 = time.time()
        S = 2 * maxabs(g, s, cache)[1:].sum()      # ell and ell - g^s
        line = "g=%d s=%d S_inf=%.6e" % (g, s, S)
        if prev is not None:
            rate = np.log(S / prev) / np.log(g)
            line += "  log_g(S(s)/S(s-1))=%.4f  c_loc=%.4f" % (rate, 2 - rate)
        print(line, "(%.0fs)" % (time.time() - t0), flush=True)
        prev = S
