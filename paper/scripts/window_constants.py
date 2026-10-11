#!/usr/bin/env python3
"""
Certified computation of the constants c_g of the paper

    "Palindromic perfect powers: an improvement of the
     Cilleruelo--Luca--Shparlinski bound"

(Section 5.4, Tables 1 and 2), together with a brute-force check of the
window bound (Lemma 5.6) for small s.

Notation follows the paper:
  f(theta) = |sin(pi g theta)| / (g |sin(pi theta)|),  f = 1 on the integers;
  a window has length w and weights lam_0, ..., lam_{w-1} (K = sum of lam_j);
  r >= 1 is the number of digits used to localise D_0, and nu = w + r - 2;
  a pattern sigma = (sigma_0, ..., sigma_{nu-1}) has the index
      p(sigma) = sum_j sigma_j g^(nu-1-j)          (sigma_0 most significant);
  D_0 lies in [v, v + g^-r] with v = 0.sigma_{r-1}...sigma_0 (base g), and
  D_m = (sigma_{r-1+m} + D_{m-1}) / g  for 1 <= m <= w-2.

For every pattern sigma the program computes an upper bound Ubar(sigma) for
U-hat(sigma) by the cell recursion of Section 5.4:

  C_0 = f^lam_0,
  C_{m+1}(y) = f(y)^lam_{m+1} * max_{0<=q<g} sup_{D_m} C_m((y + D_m + q)/g),

where y runs over the closed cells [n/N, (n+1)/N] and D_m runs over its
interval [num_m, num_m + 1] / g^(r+m).  The preimages of a cell are covered by
blocks of cells computed in exact integer arithmetic.  The cell bounds for f
are evaluated in 40-digit decimal arithmetic, multiplied by 1 + SAFETY and
rounded upward to double precision; the factor (1 + SAFETY)^lam carried by
each cell bound f^lam < 1 dominates the rounding errors of the subsequent
double-precision powers and products.  Then
M[(sigma_0..sigma_{nu-2}), (sigma_1..sigma_{nu-1})] = Ubar(sigma)^(1/K), and
for the positive vector x produced by power iteration

  rho_CW = (1 + SAFETY) * max_i (M x)_i / x_i

is an upper bound for the quantity rho_x of Proposition 5.7 (the final factor
dominates the rounding errors of the last stage), so that
c_g = 1 - log(rho_CW) / log(g) is admissible in Theorem 1.2.

Usage (Python 3 with NumPy):
  python3 window_constants.py run g w r [N]       one base (triangular weights)
  python3 window_constants.py table [g ...]       the rows of Table 2 (slow)
  python3 window_constants.py check g s w r [N]   brute-force check of
                                                  Lemma 5.6 for all ell
The full table takes about an hour on one core; N = 8192 throughout.
"""
import math
import sys
import time
from decimal import Decimal, getcontext, localcontext

import numpy as np

SAFETY = 1e-12

# Parameters of Table 2: g -> (w, r).  All with triangular weights, N = 8192.
TABLE = {2: (14, 5), 3: (10, 3), 4: (7, 3), 5: (6, 3), 6: (6, 2), 7: (6, 2),
         8: (5, 2), 9: (5, 2), 10: (6, 1), 12: (5, 2), 16: (4, 2)}


def triangular(w):
    """Triangular weights lam_j = min(j + 1, w - j)."""
    return [min(j + 1, w - j) for j in range(w)]


def _pi():
    """pi to the current decimal precision (Machin's formula)."""
    with localcontext() as ctx:
        ctx.prec += 10
        eps = Decimal(10) ** (-ctx.prec - 2)

        def arctan_inv(x):                         # arctan(1/x)
            x = Decimal(x)
            term = 1 / x
            total, n, sign = term, 1, -1
            while True:
                term /= x * x
                t = term / (2 * n + 1)
                if t < eps:
                    return total
                total += sign * t
                sign, n = -sign, n + 1

        p = 4 * (4 * arctan_inv(5) - arctan_inv(239))
    return +p


def _sin_pi_table(N):
    """S[j] = sin(pi j / N) for 0 <= j <= N // 2, to about 40 digits."""
    PI = _pi()
    eps = Decimal(10) ** (-getcontext().prec - 5)
    S = []
    for j in range(N // 2 + 1):
        x = PI * j / N
        term, total, n = x, x, 1
        while abs(term) > eps:                     # Taylor series
            term = -term * x * x / ((2 * n) * (2 * n + 1))
            total += term
            n += 1
        S.append(total)
    return S


def f_cell_bounds(g, N):
    """fb[n] >= sup of f over the closed cell [n/N, (n+1)/N], 0 <= n < N.

    The bound is evaluated in 40-digit decimal arithmetic, multiplied by
    1 + SAFETY, and rounded upward to double precision.
    """
    with localcontext() as ctx:
        ctx.prec = 40
        S = _sin_pi_table(N)

        def abs_sin(k):                            # |sin(pi k / N)|
            k %= N
            return S[min(k, N - k)]

        one, margin = Decimal(1), 1 + Decimal(SAFETY)
        fb = np.ones(N)                 # cells 0 and N-1 contain an integer
        for n in range(1, N - 1):
            # |sin(pi g theta)| can reach 1 on the cell iff g*cell contains
            # o/2 with o odd; otherwise it is maximal at an endpoint.
            olo = -((-2 * g * n) // N)             # ceil(2 g n / N)
            ohi = (2 * g * (n + 1)) // N           # floor(2 g (n + 1) / N)
            if olo + 1 - (olo % 2) <= ohi:
                num = one
            else:
                num = max(abs_sin(g * n), abs_sin(g * (n + 1)))
            # sin(pi theta) > 0 is concave on the cell: minimal at an endpoint.
            den = min(abs_sin(n), abs_sin(n + 1))
            b = num / (g * den) * margin
            if b < one:
                x = float(b)
                if Decimal(x) < b:
                    x = math.nextafter(x, math.inf)
                fb[n] = x
    return fb


def _range_max_table(C, j):
    """T[:, q] = max(C[:, q], ..., C[:, q + 2^j - 1]), indices mod N."""
    T = C
    for i in range(j):
        T = np.maximum(T, np.roll(T, -(1 << i), axis=1))
    return T


def dp_step(g, N, C, num, den, fpow):
    """One step C_m -> C_{m+1} of the cell recursion.

    C[b, n] bounds C_m on the closed cell n, for the pattern prefix in row b,
    whose D_m lies in [num[b], num[b] + 1] / den.  For the branch q, the
    preimage of the cell n is contained in the closed cells q0..q1 with
        q0 = floor((n + a0 + q N) / g),   q1 = floor((n + 1 + a1 + q N) / g),
    where a0 = floor(N num / den) and a1 = floor(N (num + 1) / den).
    """
    a0 = (N * num) // den
    a1 = (N * (num + 1)) // den
    spread = (1 + a1 - a0) // g                # q1 - q0 is spread or spread + 1
    Lmin = int(spread.min()) + 1
    Lmax = int(spread.max()) + 2
    j = Lmin.bit_length() - 1                  # 2^j <= Lmin
    T = _range_max_table(C, j)
    nblocks = -(-Lmax // (1 << j))
    n = np.arange(N, dtype=np.int64)[None, :]
    best = None
    for q in range(g):
        q0 = (n + (a0 + N * q)[:, None]) // g
        q1 = (n + 1 + (a1 + N * q)[:, None]) // g
        last = q1 - (1 << j) + 1               # start of the last block
        assert (last >= q0).all()
        val = None
        for t in range(nblocks):
            start = np.minimum(q0 + t * (1 << j), last) % N
            blk = np.take_along_axis(T, start, axis=1)
            val = blk if val is None else np.maximum(val, blk)
        assert (q0 + nblocks * (1 << j) - 1 >= q1).all()
        best = val if best is None else np.maximum(best, val)
    return fpow[None, :] * best


def window_bounds(g, lam, r, N, max_rows=512):
    """Return Ubar[p] >= U-hat(sigma) for all g^nu patterns, indexed by p(sigma)."""
    w = len(lam)
    nu = w + r - 2
    assert w >= 2 and r >= 1 and nu >= 2
    fb = f_cell_bounds(g, N)
    fpow = [fb ** k for k in lam]
    Ubar = np.full(g ** nu, -1.0)

    def recurse(C, num, idx, m):
        # C bounds C_m; num/g^(r+m-1) is the left end of the D_{m-1} interval.
        if m == w - 1:
            Ubar[idx] = C.max(axis=1)
            return
        B = C.shape[0]
        if B * g > max_rows and B > 1:
            h = B // 2
            recurse(C[:h], num[:h], idx[:h], m)
            recurse(C[h:], num[h:], idx[h:], m)
            return
        d = np.tile(np.arange(g, dtype=np.int64), B)      # sigma_{r-1+m}
        num2 = d * g ** (r + m - 1) + np.repeat(num, g)    # D_m interval
        C2 = dp_step(g, N, np.repeat(C, g, axis=0), num2, g ** (r + m),
                     fpow[m + 1])
        recurse(C2, num2, np.repeat(idx, g) * g + d, m + 1)

    for p0 in range(g ** r):
        sig = [(p0 // g ** (r - 1 - j)) % g for j in range(r)]  # sigma_0..
        num0 = sum(sig[i] * g ** i for i in range(r))          # v = num0/g^r
        num0 = np.array([num0], dtype=np.int64)
        C1 = dp_step(g, N, fpow[0][None, :].copy(), num0, g ** r, fpow[1])
        recurse(C1, num0, np.array([p0], dtype=np.int64), 1)
    assert (Ubar > 1e-280).all()       # far from underflow (Section 5.4)
    return Ubar


def certified_rho(g, nu, wt, iters=200000, tol=1e-15):
    """Collatz--Wielandt upper bound for the matrix M with entries wt."""
    nS = g ** (nu - 1)
    p = np.arange(g ** nu, dtype=np.int64)
    src, dst = p // g, p % nS

    def M(x):
        return np.bincount(src, weights=wt * x[dst], minlength=nS)

    x = np.ones(nS)
    for _ in range(iters):
        y = M(x)
        y /= y.max()
        done = np.max(np.abs(y - x)) < tol
        x = y
        if done:
            break
    rho = float(np.max(M(x) / x)) * (1.0 + SAFETY)
    return rho, float(x.max() / x.min())


def run(g, w, r, N=8192, lam=None):
    lam = triangular(w) if lam is None else lam
    t0 = time.time()
    Ubar = window_bounds(g, lam, r, N)
    nu = w + r - 2
    rho, vratio = certified_rho(g, nu, Ubar ** (1.0 / sum(lam)))
    c = 1.0 - math.log(rho) / math.log(g)
    print("g=%2d w=%2d r=%d N=%d lam=%s  rho_CW=%.9f  c_g>=%.6f  "
          "(max v/min v=%.2f, %.0fs)" % (g, w, r, N, ",".join(map(str, lam)),
                                         rho, c, vratio, time.time() - t0),
          flush=True)
    return rho, c


def check(g, s, w, r, N=4096, lam=None):
    """Compare max_a |Psi_ell(a)| with the bound of Lemma 5.6 for every ell."""
    lam = triangular(w) if lam is None else lam
    K = sum(lam)
    nu = w + r - 2
    Ubar = window_bounds(g, lam, r, N)
    Q = g ** s
    m = np.arange(Q, dtype=np.int64)
    rev = np.zeros(Q, dtype=np.int64)
    t = m.copy()
    for _ in range(s):
        rev = rev * g + t % g
        t //= g
    worst, S_inf, S_bound = 0.0, 0.0, 0.0
    for ell in range(1, Q):
        h = np.exp(-2j * np.pi * ((ell * rev) % Q) / Q)
        exact = np.abs(np.fft.fft(h)).max() / Q        # max_a |Psi_ell(a)|/g^s
        lp = ((g * g - 1) * ell) % Q
        dig = [(lp // g ** i) % g for i in range(s)]   # ell'_0, ..., ell'_{s-1}
        bound = 1.0
        for i in range(s - w + 1):
            p = 0
            for jj in range(i + 2 - r, i + w):         # sigma^(i)
                p = p * g + (dig[jj] if jj >= 0 else 0)
            bound *= Ubar[p] ** (1.0 / K)
        worst = max(worst, exact / bound)
        S_inf += 2 * Q * exact
        S_bound += 2 * Q * bound
    print("g=%d s=%d w=%d r=%d N=%d: max over ell of exact/bound = %.6f "
          "(must be <= 1);  S_inf(s) = %.6e <= %.6e" % (g, s, w, r, N, worst,
                                                       S_inf, S_bound),
          flush=True)
    return worst


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(0)
    cmd, args = sys.argv[1], [int(a) for a in sys.argv[2:]]
    if cmd == "run":
        run(*args)
    elif cmd == "table":
        for g in (args or sorted(TABLE)):
            run(g, *TABLE[g])
    elif cmd == "check":
        check(*args)
    else:
        print(__doc__)
