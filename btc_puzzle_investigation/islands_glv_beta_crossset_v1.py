#!/usr/bin/env python3
"""
islands_glv_beta_crossset_v1.py -- execute PREREG_islands_glv_beta_crossset_v1.md VERBATIM.
GLV/mu3 beta-image cross-structure of the Dirichlet-island curve image. Exact integers.

G1 (PRIMARY): #{ordered (i,j), i!=j : X_i == beta*X_j  OR  X_i == beta^2*X_j (mod p)}
              -> islands that are phi-related points (P_i = +-phi^{+-1}(P_j), d_i == +-lam^{+-1} d_j).
G2 (SECONDARY): #{(i,j,k) distinct : x(P_i (+) phi(P_j)) == X_k}  <=>  d_i + lam d_j == +-d_k.
Null-B random scalars (matched); AP structured-inert; PC-phi/phi^2/G2 planted positives (must fire);
C-add tautological additive control. Null of G1,G2 is a point-mass at ~0 (2M^2/p, 2M^3/p) => 1 hit fires.
Decision: p_MC=(1+#{b:S(NullB_b)>=S(arm)})/(B+1); FIRES iff p_MC <= alpha*=0.05/6=1/120.
"""
import sys, random
from islands_curveimage_jointset_v1 import (
    P, N_ORD, GX, GY, mul_jac, points_affine, build_islands, build_ap, null_scalars)

BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
assert pow(BETA, 3, P) == 1 and BETA != 1, "beta not a nontrivial cube root of 1 mod p"
ALPHA = (1, 120)  # 0.05/6


def find_lambda():
    """cube root of unity mod N_ORD with x(lam*G) == beta*x(G)."""
    rr = random.Random(12345)
    lam = 1
    while lam == 1:
        g = rr.randrange(2, N_ORD)
        lam = pow(g, (N_ORD - 1) // 3, N_ORD)
    for cand in (lam, lam * lam % N_ORD):
        Xc, Yc = points_affine([cand])[0]
        if Xc == (BETA * GX) % P:
            return cand
    raise RuntimeError("no lambda with x(lam G)=beta Gx")

LAM = find_lambda()


# ---- statistics ----
def stat_G1(pts):
    """#{ordered (i,j), i!=j : X_i == beta X_j or beta^2 X_j}. Returns (count, hit_list)."""
    d = {}
    for i, (x, y) in enumerate(pts):
        d.setdefault(x, []).append(i)
    b = BETA; b2 = BETA * BETA % P
    g1 = 0; hits = []
    for j, (x, y) in enumerate(pts):
        for target, tag in ((b * x % P, 'b'), (b2 * x % P, 'b2')):
            lst = d.get(target)
            if lst:
                for i in lst:
                    if i != j:
                        g1 += 1
                        if len(hits) < 20:
                            hits.append((i, j, tag))
    return g1, hits


def _inv(a):
    return pow(a % P, P - 2, P)


def ec_add(Pt, Qt):
    if Pt is None:
        return Qt
    if Qt is None:
        return Pt
    x1, y1 = Pt; x2, y2 = Qt
    if x1 == x2:
        if (y1 + y2) % P == 0:
            return None
        m = (3 * x1 * x1) % P * _inv(2 * y1) % P
    else:
        m = (y2 - y1) % P * _inv(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    y3 = (m * (x1 - x3) - y1) % P
    return (x3, y3)


def batch_inv(vals):
    """Montgomery batch inverse mod P: one pow-inverse for the whole list."""
    if not vals:
        return []
    pref = [1] * (len(vals) + 1)
    for i, v in enumerate(vals):
        pref[i + 1] = pref[i] * v % P
    inv = pow(pref[-1], P - 2, P)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = inv * pref[i] % P
        inv = inv * vals[i] % P
    return out


def stat_G2(pts):
    """#{(i,j,k) distinct : x(P_i (+) phi(P_j)) == X_k}. O(M^2) mults, M batch-inverses (fast)."""
    xset = {}
    for i, (x, y) in enumerate(pts):
        xset.setdefault(x, []).append(i)
    g2 = 0; hits = []
    M = len(pts); b = BETA
    for i in range(M):
        xi, yi = pts[i]
        dens = []; meta = []; specials = []
        for j in range(M):
            if j == i:
                continue
            xj, yj = pts[j]
            bxj = b * xj % P
            den = (bxj - xi) % P
            if den == 0:
                specials.append(j)               # shared x: doubling or infinity (rare)
            else:
                dens.append(den); meta.append((j, bxj, yj))
        invs = batch_inv(dens)
        for t, (j, bxj, yj) in enumerate(meta):
            m = (yj - yi) * invs[t] % P
            xq = (m * m - xi - bxj) % P
            lst = xset.get(xq)
            if lst:
                for k in lst:
                    if k != i and k != j:
                        g2 += 1
                        if len(hits) < 20:
                            hits.append((i, j, k))
        for j in specials:
            Q = ec_add((xi, yi), (b * pts[j][0] % P, pts[j][1]))
            if Q is not None:
                for k in xset.get(Q[0], ()):
                    if k != i and k != j:
                        g2 += 1
    return g2, hits


def scalar_add_control(ds):
    """C-add: #{ordered (i,j,k) distinct : d_i + d_j == +-d_k mod N_ord} -- tautological additive."""
    s = {}
    for k, dk in enumerate(ds):
        s.setdefault(dk % N_ORD, []).append(k)
        s.setdefault((-dk) % N_ORD, []).append(k)
    c = 0
    M = len(ds)
    for i in range(M):
        for j in range(M):
            if i == j:
                continue
            t = (ds[i] + ds[j]) % N_ORD
            for k in s.get(t, ()):
                if k != i and k != j:
                    c += 1
    return c


def pval(arm, nulls):
    B = len(nulls)
    return (1 + sum(1 for s in nulls if s >= arm), B + 1)


def fires(pv):
    num, den = pv
    return num * ALPHA[1] <= ALPHA[0] * den


def build_pc_phi(N, M, c, power):
    """(M-2c) islands + c phi^power pairs {d_a G, (lam^power d_a) G}."""
    isl = build_islands(N, M)
    ds = isl[:M - 2 * c]
    lo = 1 << (N - 1)
    lp = LAM if power == 1 else (LAM * LAM % N_ORD)
    da0 = lo + 12345
    for a in range(c):
        da = da0 + a
        ds.append(da); ds.append((lp * da) % N_ORD)
    return ds


def build_pc_g2(N, M):
    """random + one triple {d_i G, d_j G, (d_i+lam d_j) G}."""
    rng = random.Random(777); lo = 1 << (N - 1)
    ds = [lo + rng.randrange(lo) for _ in range(M - 3)]
    di = lo + 101; dj = lo + 202
    ds += [di, dj, (di + LAM * dj) % N_ORD]
    return ds


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 1024
    B = int(sys.argv[3]) if len(sys.argv) > 3 else 999
    do_g2 = (len(sys.argv) > 4 and sys.argv[4] == 'g2')
    print(f"# GLV beta cross-set test | N={N} M={M} B={B} | lambda={hex(LAM)[:14]}... g2={do_g2}")
    print(f"# alpha*=1/120; G1/G2 null = point-mass at ~0 (one exact GLV relation fires)")

    islands = build_islands(N, M)
    ap = build_ap(islands, N)
    Pi = points_affine(islands); Pa = points_affine(ap)
    g1_isl, hits_isl = stat_G1(Pi)
    g1_ap, _ = stat_G1(Pa)
    cadd = scalar_add_control(islands[:min(M, 400)])   # tautological control (subset for speed)

    # Null-B
    rng = random.Random(20260721)
    g1_n = []
    for b in range(B):
        Pn = points_affine(null_scalars(N, M, rng))
        g1_n.append(stat_G1(Pn)[0])
        if (b + 1) % 200 == 0:
            print(f"#   G1 null {b+1}/{B}", flush=True)

    # planted positives
    g1_pcphi = stat_G1(points_affine(build_pc_phi(N, M, 1, 1)))[0]
    g1_pcphi2 = stat_G1(points_affine(build_pc_phi(N, M, 1, 2)))[0]

    print("\n=== G1  exact GLV-orbit collision (PRIMARY) ===")
    print(f"  islands G1 = {g1_isl}   hits(sample)={hits_isl[:6]}")
    print(f"  AP      G1 = {g1_ap}")
    print(f"  Null-B  G1: min={min(g1_n)} max={max(g1_n)} nonzero={sum(1 for v in g1_n if v>0)}/{B}")
    pv = pval(g1_isl, g1_n)
    print(f"  p_MC(islands) = {pv[0]}/{pv[1]}  -> {'FIRES' if fires(pv) else 'null'}"
          f"   (AP {'FIRES' if fires(pval(g1_ap,g1_n)) else 'null'})")
    print(f"  PLANTED: PC-phi G1={g1_pcphi} (expect 2) -> {'FIRES' if fires(pval(g1_pcphi,g1_n)) else 'FAIL'}"
          f" | PC-phi^2 G1={g1_pcphi2} (expect 2) -> {'FIRES' if fires(pval(g1_pcphi2,g1_n)) else 'FAIL'}")
    print(f"  CONTROL C-add (islands, tautological additive) = {cadd}  (band-impossible => expect 0)")

    if do_g2:
        Bg2 = min(B, 199)
        print(f"\n=== G2  3-island GLV-additive closure (SECONDARY, M={M}, B={Bg2}) ===")
        g2_isl, h2 = stat_G2(Pi)
        g2_pc = stat_G2(points_affine(build_pc_g2(N, M)))[0]
        rng2 = random.Random(20260722); g2_n = []
        for b in range(Bg2):
            g2_n.append(stat_G2(points_affine(null_scalars(N, M, rng2)))[0])
        pv2 = pval(g2_isl, g2_n)
        print(f"  islands G2 = {g2_isl}  hits={h2[:6]}")
        print(f"  Null-B G2: min={min(g2_n)} max={max(g2_n)} nonzero={sum(1 for v in g2_n if v>0)}/{Bg2}")
        print(f"  p_MC(islands) = {pv2[0]}/{pv2[1]}  -> {'FIRES' if fires(pv2) else 'null'}")
        print(f"  PLANTED PC-G2 = {g2_pc} (expect >=1) -> {'FIRES' if fires(pval(g2_pc,g2_n)) else 'FAIL'}")

    print(f"\n# primary cell = G1 @ N=128, M=1024.")


if __name__ == "__main__":
    main()
