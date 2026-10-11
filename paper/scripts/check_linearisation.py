#!/usr/bin/env python3
"""
Randomised exact checks of Lemmas 3.2 and 3.3 (sizes of the nodes and the
g-adic / archimedean linearisations), followed by a check of Lemma 3.3(c) on
actual palindromic powers (base-10 squares, base-2 cubes, base-3 squares):
for x^k in P_{g,L} and all admissible (t, s),
  lambda_b(z) - rev_s(n_b(z)) lies in [-1/g, 1).
All arithmetic that matters is exact (integers and fractions).

Usage:  python3 check_linearisation.py      (a few minutes)
"""
import random, math
from fractions import Fraction as Fr
random.seed(7)
def rev(n, j, g):
    r = 0
    for _ in range(j): r = r*g + n % g; n //= g
    return r
def iroot_ceil(y, k):   # least x with x^k >= y
    x = int(round(y ** (1.0/k))) if y < 10**300 else int(math.exp(math.log(y)/k))
    while x**k < y: x += 1
    while x > 0 and (x-1)**k >= y: x -= 1
    return x
bad = 0; tests = 0
for _ in range(3000):
    g = random.choice([2,3,4,5,6,7,10,12,16]); k = random.choice([2,2,3,4])
    t = random.randint(3, 7); s = random.randint(1, t-2)
    L = random.randint(2*(t+s), 2*(t+s)+12)
    while True:
        b = random.randrange(g**t)
        if (b**k) % g: break
    T = rev(b**k % g**t, t, g)
    assert g**(t-1) <= T < g**t
    y0 = T*g**(L-t); y1 = (T+1)*g**(L-t)
    xlo = iroot_ceil(y0, k); xhi = iroot_ceil(y1, k)       # I_b ∩ Z = [xlo, xhi)
    X1 = g**(L/k)
    Z = X1 * g**(-2*t)
    # Z_b and x_b
    first = xlo + ((b - xlo) % g**t)
    Zb = 0 if first >= xhi else (xhi - 1 - first)//g**t + 1
    lenI = y1**(1.0/k) - y0**(1.0/k)
    tests += 1
    if not (Z/k*(1-1e-9) <= lenI/g**t <= g*Z/k*(1+1e-9)): bad += 1; print("sizes |I_b| fail", g,k,t,s,L,b)
    if not (Z/k - 1 - 1e-9 <= Zb <= g*Z/k + 1 + 1e-9): bad += 1; print("Z_b fail", g,k,t,s,L,b,Zb,Z)
    if Zb == 0: continue
    xb = first
    beta = k*b**(k-1) % g**s
    alpha = (xb**k // g**t) % g**s
    deltab = Fr(k*xb**(k-1)) * Fr(g)**(2*t+s-L)
    deltaT = k*(T*g**(L-t))**((k-1)/k) * g**(2*t+s-L)
    if not (-1e-9 <= float(deltab) - deltaT <= g**(1-t)*deltaT*(1+1e-9)): bad += 1; print("delta fail")
    if not (k/(2*g)*g**s/Z*(1-1e-9) <= deltaT <= k*g**s/Z*(1+1e-9)): bad += 1; print("delta(T) range fail")
    for z in random.sample(range(Zb), min(Zb, 5)):
        x = xb + g**t*z
        xk = x**k
        assert (xk // g**(L-t)) == T    # x in I_b
        na = (xk // g**t) % g**s
        if na != (alpha + beta*z) % g**s: bad += 1; print("lin(a) fail")
        nb = (xk // g**(L-t-s)) % g**s
        phi = Fr(xk, g**(L-t-s)) - T*g**s
        if nb != math.floor(phi): bad += 1; print("lin(b) floor fail")
        lam = (Fr(xb**k, g**(L-t-s)) - T*g**s) + deltab*z
        dif = phi - lam
        if not (0 <= dif <= Fr(k-1, k)*Fr(g)**(s+1-t)): bad += 1; print("lin(b) bound fail", float(dif))
print("tests", tests, "failures", bad)
# Lemma 3.3(c) on actual palindromic powers, base 10 squares and base 2 cubes
def is_pal(n, g):
    d = []
    while n: d.append(n % g); n //= g
    return d == d[::-1], len(d)
cnt = 0
for g, k, xmax in ((10, 2, 3*10**6), (2, 3, 2**17), (3, 2, 3**11)):
    for x in range(1, xmax):
        if x % g == 0: continue
        p, L = is_pal(x**k, g)
        if not p or L < 10: continue
        for t in range(3, L//2):
            for s in range(1, t-1):
                if t + s > L/2: continue
                b = x % g**t
                T = rev(b**k % g**t, t, g)
                y0 = T*g**(L-t); xlo = iroot_ceil(y0, k)
                xb = xlo + ((b - xlo) % g**t); z = (x - xb)//g**t
                assert (x - xb) % g**t == 0 and z >= 0
                beta = k*b**(k-1) % g**s; alpha = (xb**k // g**t) % g**s
                lam = (Fr(xb**k, g**(L-t-s)) - T*g**s) + Fr(k*xb**(k-1))*Fr(g)**(2*t+s-L)*z
                n = (alpha + beta*z) % g**s
                d = lam - rev(n, s, g)
                cnt += 1
                if not (Fr(-1, g) <= d < 1): print("lin(c) FAIL", g, k, x, t, s, float(d))
print("lin(c) checked on", cnt, "(x,t,s) triples from actual palindromic powers")
