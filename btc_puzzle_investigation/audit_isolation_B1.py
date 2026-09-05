# audit_isolation_B1.py  --  sage audit_isolation_B1.py
# DECISIVE suppression-check: does v3's exact twist (j0 = B=1) show T1_j0 ~ +0.21 under v4's PROPER
# #E-bracketed matching + random_point targets? If null -> v3's signal was the improper method (artifact).
# If ~+0.21 -> B=1 is genuinely special, the "artifact" conclusion is wrong (a suppression).
from sage.all import *
import random, math, json, sys
H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'h'}; exec(open(H).read(), _g); measure_system = _g['measure_system']

def order(F, A, B): return int(EllipticCurve(F, [A, B]).order())

def decomp_target(E, F, m, extra):
    for _ in range(300):
        pts = [E.random_point() for _ in range(m)]
        if any(P == E(0) for P in pts): continue
        xs = [P[0] for P in pts]
        if len(set(xs)) < m: continue
        S = E(0)
        for P in pts: S = S + P
        T = -S
        if T == E(0): continue
        V = list(xs)
        for _ in range(extra):
            Q = E.random_point()
            if Q != E(0): V.append(Q[0])
        if len(set(V)) < m+extra: continue
        return T[0], V
    return None

def cell_logQ(F, A, B, m, extra, K, seed0):
    Dmax = 2**(m-1) + m*(m+extra) + 5; E = EllipticCurve(F, [A, B]); qs = []
    for k in range(K):
        set_random_seed(int(seed0+k)); random.seed(int(seed0+k))
        dt = decomp_target(E, F, m, extra)
        if dt is None: continue
        t, V = dt; r = measure_system(F, A, B, m, t, V, Dmax)
        if r['dim'] == 0 and r['quo'] is not None: qs.append(int(r['quo']))
    return (math.log(sum(qs)/len(qs)) if qs else None)

def main():
    m, extra, K = 3, 1, 25
    primes = [int(p) for p in prime_range(500, 1500) if p % 3 == 1][:12]
    T1s = []
    print("B=1 (v3 twist) under PROPER #E-bracketed matching:")
    for p in primes:
        F = GF(p); random.seed(int(1000+p)); set_random_seed(int(1000+p))
        o_cm = order(F, 0, 1)                       # j0 = (0,1), v3's exact twist
        # draw non-CM that BRACKET B=1's #E (>=2 below, >=2 above), cap 16
        ncm = []; tries = 0
        while len(ncm) < 16 and tries < 30000:
            tries += 1
            A = random.randrange(1, p); B = random.randrange(1, p)
            if (4*A**3+27*B**2) % p == 0: continue
            E = EllipticCurve(F, [A, B]); j = E.j_invariant()
            if j == F(0) or j == F(1728): continue
            ncm.append(dict(A=int(A), B=int(B), order=int(E.order())))
            below = sum(1 for c in ncm if c['order'] < o_cm)
            above = sum(1 for c in ncm if c['order'] > o_cm)
            if len(ncm) >= 8 and below >= 2 and above >= 2: break
        below = sum(1 for c in ncm if c['order'] < o_cm); above = sum(1 for c in ncm if c['order'] > o_cm)
        if below < 2 or above < 2:
            print("  p=%d DROPPED (B=1 not bracketable)" % p); continue
        qj0 = cell_logQ(F, 0, 1, m, extra, K, seed0=7000)
        near = min(ncm, key=lambda c: abs(c['order']-o_cm))
        qnc = cell_logQ(F, near['A'], near['B'], m, extra, K, seed0=7000)
        if qj0 is None or qnc is None:
            print("  p=%d no quo" % p); continue
        t1 = qj0 - qnc; T1s.append(t1)
        print("  p=%-5d a_p(B=1)=%+d  T1=%+.3f  #Egap=%.4f" % (p, p+1-o_cm, t1, abs(o_cm-near['order'])/float(p)))
    if T1s:
        mean = sum(T1s)/len(T1s)
        # sign-flip null
        random.seed(999); R = 20000; obs = mean; ge = 0
        for _ in range(R):
            s = sum(d*random.choice((1, -1)) for d in T1s)/len(T1s)
            if s >= obs-1e-12: ge += 1
        pv = (ge+1.0)/(R+1.0)
        print("\nB=1 pooled T1 = %+.4f  (n=%d, pos %d/%d)  one-sided perm_p=%.4f" %
              (mean, len(T1s), sum(1 for x in T1s if x > 0), len(T1s), pv))
        print("v3 reported T1_j0=+0.21.  This B=1-under-proper-matching value is the decisive comparison.")

main()
