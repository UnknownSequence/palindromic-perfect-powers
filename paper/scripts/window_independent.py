#!/usr/bin/env python3
"""
Independent implementation of the window bound (Proposition 5.7 and Section 5.4
of the paper), written separately from window_constants.py as a cross-check.
It reproduces the rho_CW values of Table 2 to all 9 printed digits.

Differences from window_constants.py: the cell bounds for f are computed in
double precision (with a 1e-13 safety factor) and the range maxima use a
doubling table; otherwise the same closed cells, exact integer covers of the
preimages, and Collatz--Wielandt bound.  It saves the bounds Ubar(sigma) as
W_g{g}_r{r}_N{N}_{spec}.npy in the current directory.

Usage:  python3 window_independent.py g r N spec [spec ...]
        spec = triW (triangular weights, window w=W), uniW (uniform), or a
        comma-separated list of integer weights.
  e.g.  python3 window_independent.py 2 5 8192 tri10        (about 15 s)
"""
import numpy as np, math, sys, time

def fcell(g, N):
    n = np.arange(N, dtype=np.int64)
    # half-integer (2h+1)/2 in [g n/N, g(n+1)/N]  <=>  odd o with 2 g n <= o N <= 2 g (n+1)
    olo = -((-2 * g * n) // N)          # ceil(2gn/N)
    ohi = (2 * g * (n + 1)) // N         # floor(2g(n+1)/N)
    first_odd = olo + (1 - (olo & 1))
    has_half = first_odd <= ohi
    # numerator max of |sin(pi g x)| at endpoints (reduce g n mod 2N for accuracy)
    s0 = np.abs(np.sin(np.pi * ((g * n) % (2 * N)) / N))
    s1 = np.abs(np.sin(np.pi * ((g * (n + 1)) % (2 * N)) / N))
    num = np.where(has_half, 1.0, np.maximum(s0, s1))
    # denominator min of |sin(pi x)| on [n/N,(n+1)/N] (concave on [0,1]) -> endpoints; exactly 0 at n=0 and n=N-1
    d0 = np.sin(np.pi * n / N); d1 = np.sin(np.pi * (N - n - 1) / N)   # sin(pi (n+1)/N) = sin(pi (N-n-1)/N)
    den = np.minimum(d0, d1)
    den[0] = 0.0; den[N - 1] = 0.0
    with np.errstate(divide='ignore', invalid='ignore'):
        fb = np.where(den > 0, num / (g * den), 1.0)
    fb = np.minimum(fb * (1 + 1e-13), 1.0)   # tiny safety factor for rounding
    return fb

def rangemax_table(C, j):
    T = C
    for i in range(j):
        T = np.maximum(T, np.roll(T, -(1 << i), axis=1))
    return T   # T[q] = max C[q .. q+2^j-1] (cyclic)

def step(g, N, C, Lnum, den, fk, nidx):
    # C: (B,N) bounds for C_m; Lnum: (B,) ints; D_m in [Lnum, Lnum+1]/den.  returns bounds for C_{m+1}
    a0 = (N * Lnum) // den
    a1 = (N * (Lnum + 1)) // den
    # cover of the preimage of closed cell n under branch k: cells q0..q1 with
    # q0=(n+a0+Nk)//g, q1=(n+1+a1+Nk)//g (exact).  L=q1-q0+1 in {floor(Delta/g)+1, floor(Delta/g)+2}, Delta=1+a1-a0.
    Delta = 1 + a1 - a0
    Lmin = int((Delta // g).min()) + 1
    Lmax = int((Delta // g).max()) + 2
    j = 0
    while (1 << (j + 1)) <= Lmin: j += 1
    T = rangemax_table(C, j)
    nb = -(-Lmax // (1 << j))       # number of blocks of length 2^j needed
    best = None
    for k in range(g):
        q0 = (nidx[None, :] + (a0 + N * k)[:, None]) // g
        q1 = (nidx[None, :] + 1 + (a1 + N * k)[:, None]) // g
        last = q1 - (1 << j) + 1
        assert (last >= q0).all()
        v = None
        for t in range(nb):
            pos = np.minimum(q0 + t * (1 << j), last) % N
            vt = np.take_along_axis(T, pos, 1)
            v = vt if v is None else np.maximum(v, vt)
        if nb == 1:   # make sure the block also reaches q1
            assert (q0 + (1 << j) - 1 >= q1).all()
        best = v if best is None else np.maximum(best, v)
    return fk[None, :] * best

def weights(g, kap, r, N, Bmax=512, verbose=False):
    w = len(kap); P = w + r - 2
    fb = fcell(g, N)
    fk = [fb ** k for k in kap]
    nidx = np.arange(N, dtype=np.int64)
    W = np.full(g ** P, -1.0)
    t0 = time.time()
    def rec(C, Lnum, idx, m):
        # C = bounds for C_m (uses D_0..D_{m-1}); Lnum = numerators of D_{m-1} (den g^(r+m-1)); idx = pattern prefix
        if m == w - 1:
            W[idx] = C.max(axis=1); return
        B = C.shape[0]
        if B * g > Bmax and B > 1:
            h = B // 2
            rec(C[:h], Lnum[:h], idx[:h], m); rec(C[h:], Lnum[h:], idx[h:], m); return
        # new digit sigma_{r-1+m}
        d = np.tile(np.arange(g, dtype=np.int64), B)
        Ln = d * g ** (r + m - 1) + np.repeat(Lnum, g)
        Cn = step(g, N, np.repeat(C, g, axis=0), Ln, g ** (r + m), fk[m + 1], nidx)
        rec(Cn, Ln, np.repeat(idx, g) * g + d, m + 1)
    # first r digits sigma_0..sigma_{r-1}
    for p0 in range(g ** r):
        dig = [(p0 // g ** (r - 1 - j)) % g for j in range(r)]     # dig[j] = sigma_j, sigma_0 most significant in p0
        L0 = sum(dig[j] * g ** j for j in range(r))                 # v = 0.sigma_{r-1}...sigma_0 = L0/g^r
        C1 = step(g, N, fk[0][None, :].copy(), np.array([L0], dtype=np.int64), g ** r, fk[1], nidx)
        rec(C1, np.array([L0], dtype=np.int64), np.array([p0], dtype=np.int64), 1)
        if verbose and p0 % max(1, g ** r // 8) == 0:
            print("  prefix", p0, "of", g ** r, "%.0fs" % (time.time() - t0), flush=True)
    assert (W > 0).all()
    return W

def rho_bounds(g, P, wt, iters=20000, tol=1e-15):
    nS = g ** (P - 1)
    p = np.arange(g ** P, dtype=np.int64)
    frm = p // g; to = p % nS
    def Mx(x): return np.bincount(frm, weights=wt * x[to], minlength=nS)
    x = np.ones(nS)
    for it in range(iters):
        y = Mx(x); lam = y.max(); y = y / lam
        if np.max(np.abs(y - x)) < tol: x = y; break
        x = y
    y = Mx(x)
    q = y / x
    return q.max(), q.min(), x.max() / x.min(), it

def tri(w): return [min(j + 1, w - j) for j in range(w)]

if __name__ == "__main__":
    g = int(sys.argv[1]); r = int(sys.argv[2]); N = int(sys.argv[3])
    for spec in sys.argv[4:]:
        kap = tri(int(spec[3:])) if spec.startswith('tri') else ([1] * int(spec[3:]) if spec.startswith('uni') else [int(x) for x in spec.split(',')])
        t0 = time.time()
        W = weights(g, kap, r, N)
        K = sum(kap); P = len(kap) + r - 2
        np.save("W_g%d_r%d_N%d_%s.npy" % (g, r, N, spec), W)
        hi, lo, vr, it = rho_bounds(g, P, W ** (1.0 / K))
        hi *= (1 + 1e-12)
        print("g=%d r=%d N=%d kappa=%s: rho in [%.9f, %.9f]  c>=%.6f (c<=%.6f for this W)  v-ratio %.3f it=%d  %.0fs" %
              (g, r, N, spec, lo, hi, 1 - math.log(hi) / math.log(g), 1 - math.log(lo) / math.log(g), vr, it, time.time() - t0), flush=True)
