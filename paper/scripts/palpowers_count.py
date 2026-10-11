#!/usr/bin/env python3
"""
Brute-force enumeration of the L-digit base-g palindromes that are perfect
k-th powers, using the Cilleruelo--Luca--Shparlinski tree (the last J digits
of x^k fix its first J digits, which confine x to a short interval, and the
residue of x mod g^J).  For each L prints:
  L, #{x : x^k is an L-digit palindrome}, (#P_{g,L})^{1/k} (the CLS scale),
  time in seconds, and the first few x if there are at most three.

Usage:  python3 palpowers_count.py g k Lmax [Lmin]
  e.g.  python3 palpowers_count.py 10 2 24 1
"""
import math, sys, time

def kroot_floor(n, k):
    if k == 2:
        return math.isqrt(n)
    x = int(round(float(n) ** (1.0 / k)))
    while x ** k > n: x -= 1
    while (x + 1) ** k <= n: x += 1
    return x

def digits(n, g):
    d = []
    while n:
        d.append(n % g); n //= g
    return d

def count(g, k, L):
    lo_all = g ** (L - 1); hi_all = g ** L
    X0 = kroot_floor(lo_all - 1, k) + 1
    X1 = kroot_floor(hi_all - 1, k)
    if X1 - X0 < 2000:
        res = [x for x in range(X0, X1 + 1) if (lambda d: d == d[::-1])(digits(x ** k, g))]
        return res
    # choose J
    best = None
    for J in range(1, L // 2 + 1):
        cost = g ** J + (X1 - X0) / g ** J * 1.0 + 0
        # candidates per residue roughly length/g^J where length ~ g^{L/k-J+1}/k
        cost = g ** J * (1 + g ** (L / k - 2 * J + 1) / k)
        if best is None or cost < best[0]:
            best = (cost, J)
    J = best[1]
    gJ = g ** J; sh = g ** (L - J)
    res = []
    for a in range(gJ):
        r = pow(a, k, gJ)
        if r % g == 0:
            continue
        # top J digits = reverse of r with J digits
        T = 0; rr = r
        for _ in range(J):
            T = T * g + rr % g; rr //= g
        lo = T * sh; hi = (T + 1) * sh
        xl = kroot_floor(lo - 1, k) + 1
        xh = kroot_floor(hi - 1, k)
        x = xl + ((a - xl) % gJ)
        while x <= xh:
            d = digits(x ** k, g)
            if d == d[::-1]:
                res.append(x)
            x += gJ
    return sorted(res)

if __name__ == "__main__":
    g = int(sys.argv[1]); k = int(sys.argv[2]); Lmax = int(sys.argv[3]); Lmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    for L in range(Lmin, Lmax + 1):
        t = time.time()
        r = count(g, k, L)
        h = L - L // 2
        B = ((g - 1) * g ** (h - 1)) ** (1 / k)
        print(L, len(r), round(B), round(time.time() - t, 1), r[:3] if len(r) <= 3 else "", flush=True)
