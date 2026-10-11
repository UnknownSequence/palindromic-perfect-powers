#!/usr/bin/env python3
"""
Random stress test of the window bound: runs `window_constants.check` (exact
max_a |Psi_ell(a)| by FFT versus the bound of Lemma 5.6 with Ubar) on fixed
edge cases and on random (g, s, w, r, N, weights), and reports the worst
ratio exact/bound (it must never exceed 1).

Usage:  python3 window_stress.py [seed] [time budget in seconds]
"""
import sys, io, os, random, contextlib, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import window_constants as wc
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
budget = float(sys.argv[2]) if len(sys.argv) > 2 else 60
t0 = time.time(); results = []
fixed = [(2,4,2,1,64,None),(2,5,5,1,64,None),(2,6,2,3,16,None),(3,3,2,1,7,None),(3,4,4,4,10,None),
         (5,3,2,1,5,None),(7,3,3,1,9,None),(16,2,2,1,4,None),(16,2,2,2,33,None),(10,3,2,1,1,None),
         (2,8,3,6,129,[0,1,0]),(3,5,3,2,100,[2,0,1]),(4,4,4,2,50,[0,0,1,0]),(6,3,3,1,77,[1,0,3]),
         (12,2,2,1,1000,None),(9,3,3,2,81,None),(8,3,3,3,512,None),(2,11,11,1,256,None),(2,10,7,7,3,None)]
cfgs = list(fixed)
gs = [2,2,2,3,3,4,5,6,7,8,9,10,12,16]
while len(cfgs) < 400:
    g = random.choice(gs)
    smax = max(2, int(12/ (g.bit_length()-0.5)))
    s = random.randint(2, smax)
    if g**s > 6000: continue
    w = random.randint(2, s)
    r = random.randint(1, 4)
    if g**(w+r-2) > 5000: continue
    N = random.choice([1,2,3,5,8,13,16,31,64,100,127,256,500,1024,2048])
    lt = random.random()
    if lt < 0.4: lam = None
    elif lt < 0.6: lam = [1]*w
    else:
        lam = [random.randint(0,3) for _ in range(w)]
        if sum(lam) == 0: lam[0] = 1
    cfgs.append((g,s,w,r,N,lam))
cfgs = [c for c in cfgs if c[2] + c[3] - 2 >= 2]     # nu = w + r - 2 >= 2 (Prop. 5.7)
worst = (0, None); n = 0
for c in cfgs:
    if time.time() - t0 > budget: break
    g,s,w,r,N,lam = c
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            x = wc.check(g,s,w,r,N,lam)
        except Exception as e:
            print("EXC", c, repr(e), file=sys.stderr); continue
    n += 1
    if x > worst[0]: worst = (x, c)
    if x > 1 - 1e-6: print("NEAR/VIOLATION", c, x, flush=True)
print("ran", n, "configs; worst ratio", worst, "time %.0fs" % (time.time()-t0))
