#!/usr/bin/env python3
"""
Turn the output of `python3 window_constants.py table` into the entries of
Tables 1 and 2 and Corollary 1.3 of the paper "Palindromic perfect powers".

Rounding conventions (as in the paper):
  rho_CW  rounded UP to 6 decimals (the logs print 9 decimals, so 1e-9 is added
          before rounding up);
  c_g   = 1 - log_g(rho_CW, rounded up), rounded DOWN to 4 decimals;
  gamma = 1 - c/(4-c) (prime powers) or 1 - c/((k-1)(4-c)+2) (other g),
          rounded UP to 4 decimals, and checked to be strictly larger than the
          exact value (so that the logarithmic factors are absorbed).

Usage:  python3 make_tables.py LOGFILE [LOGFILE ...]
"""
import math
import re
import sys
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR

TABLE = {2: (14, 5), 3: (10, 3), 4: (7, 3), 5: (6, 3), 6: (6, 2), 7: (6, 2),
         8: (5, 2), 9: (5, 2), 10: (6, 1), 12: (5, 2), 16: (4, 2)}
PRIME_POWERS = (2, 3, 4, 5, 7, 8, 9, 16)
OTHER = (6, 10, 12)


def read_runs(files):
    rho = {}
    pat = re.compile(r"g=\s*(\d+) w=\s*(\d+) r=(\d) N=8192 lam=([\d,]+)\s+rho_CW=([\d.]+)")
    for fn in files:
        for line in open(fn):
            m = pat.match(line)
            if not m:
                continue
            g, w, r = int(m[1]), int(m[2]), int(m[3])
            lam = [int(x) for x in m[4].split(',')]
            if TABLE.get(g) == (w, r) and lam == [min(j + 1, w - j) for j in range(w)]:
                rho[g] = Decimal(m[5])
    return rho


def ceil_d(x, nd):
    return x.quantize(Decimal(1).scaleb(-nd), rounding=ROUND_CEILING)


def floor_d(x, nd):
    return x.quantize(Decimal(1).scaleb(-nd), rounding=ROUND_FLOOR)


def main(files):
    rho = read_runs(files)
    cg = {}
    print("Table 2 rows (g & w & r & rho_CW & c_g):")
    for g in sorted(rho):
        w, r = TABLE[g]
        rho_up = ceil_d(rho[g] + Decimal("1e-9"), 6)
        c = 1 - math.log(float(rho_up)) / math.log(g)
        cg[g] = floor_d(Decimal(repr(c)), 4)
        print("%d & %d & %d & %s & %s\\\\" % (g, w, r, rho_up, cg[g]))
    print("\nTable 1 (c_g):", " & ".join("%d: %s" % (g, cg[g]) for g in sorted(cg)))
    print("\nCorollary 1.3, prime powers (every k):")
    for g in PRIME_POWERS:
        if g in cg:
            c = float(cg[g]); x = 1 - c / (4 - c)
            up = ceil_d(Decimal(repr(x)), 4); assert float(up) > x
            print("  g=%2d gamma=%s (exact %.6f)" % (g, up, x))
    print("Corollary 1.3, other bases:")
    for k in (2, 3):
        for g in OTHER:
            if g in cg:
                c = float(cg[g]); assert c <= math.log(2) / (2 * math.log(g))
                x = 1 - c / ((k - 1) * (4 - c) + 2)
                up = ceil_d(Decimal(repr(x)), 4); assert float(up) > x
                print("  g=%2d k=%d gamma=%s (exact %.6f)" % (g, k, up, x))
                if g == 10 and k == 2:
                    print("        base-10 squares: exponent gamma/2 = %.6f -> %s"
                          % (x / 2, ceil_d(Decimal(repr(x / 2)), 4)))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
    else:
        main(sys.argv[1:])
