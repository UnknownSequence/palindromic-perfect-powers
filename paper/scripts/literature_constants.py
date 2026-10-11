#!/usr/bin/env python3
"""
What the published / preprint sup-norm bounds give for S_inf (for comparison
with Table 1 of the paper), evaluated numerically and summed over ell:
  * Dartyge-Martin-Rivat-Shparlinski-Swaenepoel, "Reversible primes", Lemma 2.6
    (base 2, arXiv v1 numbering): prod_j (|cos(pi 3 l 2^j/2^s)|/4 + 3/4)^(1/3);
  * Bhowmik-Suzuki, arXiv:2406.13334v1, Lemma 4.9 (any base):
    exp(-(pi^2/12)((g-1)/(g+1)) sum_i ||(g^2-1) g^i l / g^s||^2).
Prints the local exponent c (so that S_inf ~ g^{(2-c)s}) between successive s.

Usage:  python3 literature_constants.py
"""
import numpy as np, math
# DMRSS Lemma 2.6 bound summed over l (g=2): sum_{l mod 2^s} prod_{j=1}^{s-3} (|cos(pi*3l2^j/2^s)|/4+3/4)^(1/3)
# BhS Lemma 4.9 bound summed over l: sum_l exp(-(pi^2/12)((g-1)/(g+1)) sum_{i=1}^{s-3} ||(g^2-1) g^i l/g^s||^2)
def dmrss(s):
    N=2**s; l=np.arange(N,dtype=np.int64); acc=np.zeros(N)
    for j in range(1,s-2):
        x=((3*l*2**j)%N)/N
        acc+=np.log(np.abs(np.cos(np.pi*x))/4+0.75)/3
    return np.exp(acc).sum()
def bhs(g,s):
    N=g**s; l=np.arange(N,dtype=np.int64); acc=np.zeros(N); C=(math.pi**2/12)*(g-1)/(g+1)
    for i in range(1,s-2):
        x=(((g*g-1)*l*g**i)%N)/N; x=np.minimum(x,1-x)
        acc+=-C*x*x
    return np.exp(acc).sum()
prev=None
for s in range(8,23,2):
    v=dmrss(s)
    if prev: print("DMRSS g=2 s=%d local c=%.4f"%(s,1-math.log(v/prev)/(2*math.log(2))))
    prev=v
prev=None
for s in range(8,23,2):
    v=bhs(2,s)
    if prev: print("BhS g=2 s=%d local c=%.4f"%(s,1-math.log(v/prev)/(2*math.log(2))))
    prev=v
prev=None
for s in range(3,7):
    v=bhs(10,s)
    if prev: print("BhS g=10 s=%d local c=%.4f"%(s,1-math.log(v/prev)/math.log(10)))
    prev=v
