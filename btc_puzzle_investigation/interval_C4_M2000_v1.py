#!/usr/bin/env python3
"""interval_C4_M2000_v1.py -- ITEM 3 / C.4: the interval channel at M = 2000.

WHY.  At M = 96 the measured detection floor was >= 35-50% of the set carrying a coherent class
bias.  That is nearly vacuous: a sparse 96-element subset of a 2^128 interval cannot show a 35%
coherent bias unless ECDLP is trivially broken.  The M=96 non-detection is therefore an
INSUFFICIENT-POWER result, not a null (retracted in RESULT_interval_sumobject_item3_v1.md).

C.4 raises M to 2000.  Pairs go 4560 -> 1,999,000, a 438x increase, so the floor (which scales like
1/sqrt(#pairs)) should improve by ~21x.  THE POINT OF THIS RUN IS THE FLOOR, not another
non-detection: the power curve is measured first and reported whatever the arms do.

Speed: gmpy2 powmod is 9x Python pow (8.6 us vs 77.4 us, measured).  One pool-wide class table is
built once; null draws are numpy lookups.

OBJECTS: the swap-invariant SUM x(P_i+P_j) and the GROUP-LAW DIFFERENCE x(P_i-P_j).
READOUTS: E2, E3, E6 (squared magnitudes of the mu_2/mu_3/mu_6 character sums over the class multiset).
CONTROLS: C-PLANT power curve (the headline), C-GLV (theorem: E3=E6=0 exactly, E2 free),
          C-NEG with the standing n>=20 repair.
"""

import sys
import time
import numpy as np
from random import Random
from gmpy2 import powmod, invert, mpz

P = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
N = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
GX = mpz(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
GY = mpz(0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
EXP6 = (P - 1)//6
BETA = powmod(mpz(2), (P - 1)//3, P)


def _z6():
    g = mpz(3)
    while powmod(g, (P-1)//2, P) == 1 or powmod(g, (P-1)//3, P) == 1:
        g += 1
    z = powmod(g, EXP6, P)
    tab = {}
    v = mpz(1)
    for j in range(6):
        tab[int(v)] = j
        v = v*z % P
    return tab


Z6 = _z6()


def mu6(d):
    d %= P
    if d == 0:
        return -1
    return Z6[int(powmod(d, EXP6, P))]


def jdbl(A):
    X, Y, Z = A
    if Y == 0:
        return (mpz(0), mpz(0), mpz(0))
    S = 4*X*Y*Y % P
    M_ = 3*X*X % P
    Xr = (M_*M_ - 2*S) % P
    return (Xr, (M_*(S - Xr) - 8*Y**4) % P, 2*Y*Z % P)


def jadd(A, B):
    X1, Y1, Z1 = A
    X2, Y2, Z2 = B
    if Z1 == 0:
        return B
    if Z2 == 0:
        return A
    Z1Z1 = Z1*Z1 % P
    Z2Z2 = Z2*Z2 % P
    U1 = X1*Z2Z2 % P
    U2 = X2*Z1Z1 % P
    S1 = Y1*Z2*Z2Z2 % P
    S2 = Y2*Z1*Z1Z1 % P
    if U1 == U2:
        return jdbl(A) if S1 == S2 else (mpz(0), mpz(0), mpz(0))
    H = (U2 - U1) % P
    R = (S2 - S1) % P
    H2 = H*H % P
    H3 = H2*H % P
    U1H2 = U1*H2 % P
    X3 = (R*R - H3 - 2*U1H2) % P
    return (X3, (R*(U1H2 - X3) - S1*H3) % P, Z1*Z2*H % P)


def jneg(A):
    return (A[0], (-A[1]) % P, A[2])


def jmul(k, Pt=(GX, GY, mpz(1))):
    R = (mpz(0), mpz(0), mpz(0))
    Q = Pt
    while k:
        if k & 1:
            R = jadd(R, Q)
        Q = jdbl(Q)
        k >>= 1
    return R


def batch_x(pts):
    zs = [p[2] for p in pts]
    pre = [mpz(1)]*(len(zs)+1)
    for i, z in enumerate(zs):
        pre[i+1] = pre[i]*z % P
    inv = invert(pre[-1], P)
    out = [None]*len(zs)
    for i in range(len(zs)-1, -1, -1):
        zi = inv*pre[i] % P
        inv = inv*zs[i] % P
        out[i] = pts[i][0]*zi % P*zi % P
    return out


def classes_of(pts, mode, pairs=None):
    n = len(pts)
    if pairs is None:
        pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
    q = []
    for i, j in pairs:
        r = jadd(pts[i], pts[j]) if mode == "sum" else jadd(pts[i], jneg(pts[j]))
        if r[2] != 0:
            q.append(r)
    return np.array([mu6(x) for x in batch_x(q)], dtype=np.int8)


def stats_np(cl):
    c = np.bincount(cl[cl >= 0], minlength=6).astype(object)
    E2 = int((c[0]+c[2]+c[4]-c[1]-c[3]-c[5])**2)
    t = [c[0]+c[3], c[1]+c[4], c[2]+c[5]]
    E3 = int(((2*t[0]-t[1]-t[2])**2 + 3*(t[1]-t[2])**2)//4)
    re = 2*c[0]+c[1]-c[2]-2*c[3]-c[4]+c[5]
    im = c[1]+c[2]-c[4]-c[5]
    E6 = int((re*re + 3*im*im)//4)
    return E2, E3, E6


def pool_pts(n, rng):
    out = []
    while len(out) < n:
        x = mpz(rng.randrange(0, int(P)))
        r = (x*x % P*x + 7) % P
        if powmod(r, (P-1)//2, P) != 1:
            continue
        out.append((x, powmod(r, (P+1)//4, P), mpz(1)))
    return out


def pool_table(pool, mode):
    n = len(pool)
    T = np.full((n, n), -1, dtype=np.int8)
    CH = 400000
    idx, q = [], []
    t0 = time.time()
    for i in range(n):
        for j in range(i+1, n):
            r = jadd(pool[i], pool[j]) if mode == "sum" else jadd(pool[i], jneg(pool[j]))
            if r[2] != 0:
                idx.append((i, j))
                q.append(r)
            if len(q) >= CH:
                for (a, b), x in zip(idx, batch_x(q)):
                    v = mu6(x)
                    T[a, b] = T[b, a] = v
                idx, q = [], []
                print("      ... row %d/%d  [%ds]" % (i, n, time.time()-t0), flush=True)
    if q:
        for (a, b), x in zip(idx, batch_x(q)):
            v = mu6(x)
            T[a, b] = T[b, a] = v
    return T


def stats_table(T, sel):
    sub = T[np.ix_(sel, sel)]
    iu = np.triu_indices(len(sel), 1)
    return stats_np(sub[iu])


def run(mode, M, R, NP, rng, arms):
    t0 = time.time()
    print("\n" + "="*88)
    print("C.4  %s OBJECT   M=%d  R=%d  pool=%d   (pairs per set = %d)"
          % (mode.upper(), M, R, NP, M*(M-1)//2))
    print("="*88, flush=True)
    pool = pool_pts(NP, rng)
    print("  building pool table (%d pairs)..." % (NP*(NP-1)//2), flush=True)
    T = pool_table(pool, mode)
    print("  table done [%ds]" % (time.time()-t0), flush=True)
    idx = np.arange(NP)
    nl = [stats_table(T, rng.sample(range(NP), M)) for _ in range(R)]
    cols = list(zip(*nl))
    q = {nm: sorted(cols[i]) for i, nm in enumerate(("E2", "E3", "E6"))}
    for nm in ("E2", "E3", "E6"):
        s = q[nm]
        print("  null %s: median=%d 95th=%d 99th=%d" % (nm, s[R//2], s[(95*R)//100], s[(99*R)//100]),
              flush=True)

    def report(tag, e):
        out = []
        for i, nm in enumerate(("E2", "E3", "E6")):
            below = sum(1 for z in q[nm] if z < e[i])
            f = "FIRE" if e[i] >= q[nm][(99*R)//100] else ""
            out.append("%s=%-13d(%3d/%d)%s" % (nm, e[i], below, R, f))
        print("   %-12s %s" % (tag, "  ".join(out)), flush=True)

    # ---- C-PLANT power curve: greedy-biased subsets diluted with random ones
    print("  -- C-PLANT power curve (THE HEADLINE) --", flush=True)
    cand = list(range(NP))
    rng.shuffle(cand)
    full = [cand.pop()]
    while len(full) < M and cand:
        bi, bh = 0, -1
        for i, c in enumerate(cand[:120]):
            row = T[c]
            h = int(np.sum(row[full] == 0))
            if h > bh:
                bi, bh = i, h
        full.append(cand.pop(bi))
    floor = None
    for frac in (100, 50, 25, 10, 5, 2, 1):
        k = max(1, M*frac//100)
        rest = [i for i in range(NP) if i not in set(full[:k])]
        sel = full[:k] + rng.sample(rest, M-k)
        e = stats_table(T, sel)
        fires = [nm for i, nm in enumerate(("E2", "E3", "E6")) if e[i] >= q[nm][(99*R)//100]]
        if fires:
            floor = frac
        print("     %3d%% planted -> fires on %s" % (frac, ",".join(fires) if fires else "NOTHING"),
              flush=True)
    print("     ==> DETECTION FLOOR at M=%d : %s%% coherent bias" % (M, floor), flush=True)

    print("  -- C-NEG (n>=20 draws, full-range scalars) --", flush=True)
    a95 = a99 = 0
    for _ in range(20):
        e = stats_np(classes_of([jmul(rng.randrange(1, int(N))) for _ in range(M)], mode))
        for i, nm in enumerate(("E2", "E3", "E6")):
            if e[i] >= q[nm][(99*R)//100]:
                a99 += 1
            elif e[i] >= q[nm][(95*R)//100]:
                a95 += 1
    print("     60 cells | above 95th: %d (expect ~3) | above 99th: %d (expect ~0.6)" % (a95, a99),
          flush=True)

    print("  -- arms --", flush=True)
    for k in arms:
        lo, hi = 2**(k-1), 2**k
        e = stats_np(classes_of([jmul(rng.randrange(lo, hi)) for _ in range(M)], mode))
        report("k=%d" % k, e)
    print("  [%ds total]" % (time.time()-t0), flush=True)


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    NP = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    R = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    rng = Random(20260801)
    for mode in ("sum", "group"):
        run(mode, M, R, NP, rng, arms=(64, 128, 135, 160))
