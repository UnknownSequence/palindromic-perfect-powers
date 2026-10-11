#!/usr/bin/env python3
"""
Exhaustive check of Lemma 4.2 (nodes with small g-part): for every node b
(b in [0, g^t), g does not divide b^k) with m = m_g(b) and m^k < 2^t,
  (i)  d_b = gcd(k b^{k-1} mod g^s, g^s) divides k m^{k-1};
  (ii) every node b' with T_{b'} = T_b has m_g(b') = m, and there are at most
       (2k)^{omega(g)} m^{k-1} such nodes;
and, for prime powers g, that every node has m_g(b)^k < g.
Here T_b = rev_t(b^k mod g^t) and s = t - 2.

Usage:  python3 check_nodes.py        (about a minute)
"""
import math
from collections import defaultdict
def rev(n, j, g):
    r = 0
    for _ in range(j): r = r*g + n % g; n //= g
    return r
def gpart(n, g):
    m = 1
    for p in [p for p in range(2, g+1) if g % p == 0 and all(p % q for q in range(2, p))]:
        while n % p == 0: n //= p; m *= p
    return m
def omega(g): return sum(1 for p in range(2, g+1) if g % p == 0 and all(p % q for q in range(2, p)))
for (g, k, t) in ((10,2,4),(10,2,5),(10,3,4),(6,2,5),(6,3,5),(12,2,4),(12,3,5),(2,2,8),(9,2,4)):
    s = t - 2
    Dmax = 2**(t/k)          # need D^k < 2^t
    nodes = [b for b in range(g**t) if (b**k) % g]
    byT = defaultdict(list)
    for b in nodes: byT[rev(b**k % g**t, t, g)].append(b)
    viol = 0; worst = 0
    for b in nodes:
        m = gpart(b, g)
        if m >= Dmax: continue
        d = math.gcd(k*b**(k-1) % g**s, g**s)
        if (k*m**(k-1)) % d: viol += 1
        T = rev(b**k % g**t, t, g)
        same = byT[T]
        if any(gpart(b2, g) != m for b2 in same): viol += 1
        bound = (2*k)**omega(g) * m**(k-1)
        worst = max(worst, len(same)/bound)
        if len(same) > bound: viol += 1
    print("g=%d k=%d t=%d: nodes=%d, violations=%d, max #fibre/bound=%.3f" % (g,k,t,len(nodes),viol,worst))
# prime power claim: every node has m_g(b) < g^(1/k)
for (g,k,t) in ((4,2,5),(8,2,5),(8,3,4),(9,2,4),(16,3,3)):
    nodes = [b for b in range(g**t) if (b**k) % g]
    print("g=%d k=%d: max m_g(b)^k over nodes = %d < g=%d ? %s" % (g,k,max(gpart(b,g)**k for b in nodes), g, max(gpart(b,g)**k for b in nodes) < g))
