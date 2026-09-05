#!/usr/bin/env python3
"""
islands_curveimage_jointset_v1.py -- execute PREREG_islands_curveimage_jointset_v1.md VERBATIM.
Curve-side JOINT-SET test of the Dirichlet reciprocal-floor islands. Exact integers (no signal-path float).

Statistics (all >= 2-point, evade single-point Weil/KS floor):
  S1 additive energy of x  (PRIMARY)   S2 multiplicative energy of x
  S3 additive energy of y              S4 windowed pair-difference concentration of x (graded)
  S0 group/scalar additive energy      (CONTROL ONLY -- tautological, = scalar lattice; never leakage)
Arms: islands (test) | Null-B random scalars (matched, seed 20260721) | AP structured-inert null
Planted positives: PC-1 (S0), PC-2 (+-pairs, curve, S1/S2/S4), PC-3 (residue AP, S1/S3), PC-4 (residue GP, S2)
Decision: p_MC=(1+#{b:S(NullB_b)>=S(arm)})/(B+1); FIRES iff p_MC<=alpha*=0.05/12=0.004167.
"""
import sys, random, bisect
from collections import Counter

# ---- secp256k1 constants (from avenue5_only.py / KNOWN_FACTS) ----
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
ALPHA = (5, 1200)  # 0.05/12 as an exact rational (5/1200 = 0.0041667)


# ---- Jacobian EC (verified group law, avenue5_only.py) ----
def _dbl(Xx, Yy, Zz):
    if Yy == 0:
        return (0, 1, 0)
    A = (Xx * Xx) % P; B = (Yy * Yy) % P; C = (B * B) % P
    D = (2 * (((Xx + B) * (Xx + B) - A - C))) % P
    E = (3 * A) % P; F = (E * E) % P
    X3 = (F - 2 * D) % P; Y3 = (E * (D - X3) - 8 * C) % P
    Z3 = (2 * Yy * Zz) % P
    return (X3, Y3, Z3)


def _add(P1, P2):
    X1, Y1, Z1 = P1; X2, Y2, Z2 = P2
    if Z1 == 0:
        return P2
    if Z2 == 0:
        return P1
    Z1Z1 = (Z1 * Z1) % P; Z2Z2 = (Z2 * Z2) % P
    U1 = (X1 * Z2Z2) % P; U2 = (X2 * Z1Z1) % P
    S1 = (Y1 * Z2 * Z2Z2) % P; S2 = (Y2 * Z1 * Z1Z1) % P
    if U1 == U2:
        if S1 != S2:
            return (0, 1, 0)
        return _dbl(X1, Y1, Z1)
    H = (U2 - U1) % P; r = (S2 - S1) % P
    HH = (H * H) % P; HHH = (H * HH) % P; V = (U1 * HH) % P
    X3 = (r * r - HHH - 2 * V) % P; Y3 = (r * (V - X3) - S1 * HHH) % P
    Z3 = (Z1 * Z2 * H) % P
    return (X3, Y3, Z3)


# precompute affine 2^i * G  (i = 0..255), once
def _build_table():
    tab = []
    Q = (GX, GY, 1)
    for _ in range(256):
        Xx, Yy, Zz = Q
        zi = pow(Zz, P - 2, P); zi2 = (zi * zi) % P
        tab.append(((Xx * zi2) % P, (Yy * zi2 * zi) % P))
        Q = _dbl(*Q)
    return tab

TABLE = _build_table()


def mul_jac(k):
    """k*G in Jacobian, via the precomputed 2^i*G table (no doublings)."""
    R = (0, 1, 0); i = 0
    while k:
        if k & 1:
            tx, ty = TABLE[i]
            R = _add(R, (tx, ty, 1))
        k >>= 1; i += 1
    return R


def points_affine(scalars):
    """list of scalars -> list of affine (X,Y) via Montgomery BATCH inversion (1 inverse/set)."""
    jac = [mul_jac(k) for k in scalars]
    # batch-invert Z's
    Zs = [j[2] for j in jac]
    pref = [1] * (len(Zs) + 1)
    for i, z in enumerate(Zs):
        pref[i + 1] = (pref[i] * z) % P
    inv = pow(pref[-1], P - 2, P)  # ONE modular inverse for the whole set
    out = []
    for i in range(len(Zs) - 1, -1, -1):
        zi = (inv * pref[i]) % P          # = 1/Z_i
        inv = (inv * Zs[i]) % P
        Xx, Yy, _ = jac[i]
        zi2 = (zi * zi) % P
        out.append(((Xx * zi2) % P, (Yy * zi2 * zi) % P))
    out.reverse()
    return out


# ---- statistics (exact integers) ----
def _energy_exact(vals, mul, mod):
    """exact energy sum_s r(s)^2 (ordered), r(s)=2*cu(s)+cd(s). Only called if a collision exists."""
    M = len(vals)
    cu = Counter(); cd = Counter()
    for i in range(M):
        vi = vals[i]
        cd[(vi * vi if mul else vi + vi) % mod] += 1
        for j in range(i + 1, M):
            cu[((vi * vals[j]) if mul else (vi + vals[j])) % mod] += 1
    E = 0
    for s in (cu.keys() | cd.keys()):
        r = 2 * cu.get(s, 0) + cd.get(s, 0)
        E += r * r
    return E


def add_energy(vals, mod=P):
    """exact additive energy. Fast path: all i<=j sums distinct <=> Sidon <=> E = 2M^2-M (point mass).
    Only falls to the O(M^2) exact sum when a genuine collision is present."""
    M = len(vals)
    seen = set(); dup = False
    for i in range(M):
        vi = vals[i]
        for j in range(i, M):
            s = (vi + vals[j]) % mod
            if s in seen:
                dup = True; break
            seen.add(s)
        if dup:
            break
    return _energy_exact(vals, False, mod) if dup else 2 * M * M - M


def mul_energy(vals, mod=P):
    """exact multiplicative energy over nonzero vals. Same Sidon fast path. Returns (E, #zeros)."""
    nz = [v % mod for v in vals if v % mod != 0]
    M = len(nz)
    seen = set(); dup = False
    for i in range(M):
        vi = nz[i]
        for j in range(i, M):
            s = (vi * nz[j]) % mod
            if s in seen:
                dup = True; break
            seen.add(s)
        if dup:
            break
    E = _energy_exact(nz, True, mod) if dup else 2 * M * M - M
    return E, len(vals) - M


def window_count(Xs, Delta):
    """S4: #ordered pairs (i,j), i!=j, cyclic |X_i - X_j| < Delta.  O(M log M)."""
    xs = sorted(Xs); M = len(xs)
    cnt = 0
    for i in range(M):
        xi = xs[i]
        hi = bisect.bisect_left(xs, xi + Delta, i + 1, M)
        cnt += hi - (i + 1)                       # forward neighbors within Delta
        # wrap-around: neighbors near p that are within Delta cyclically
        if xi < Delta:
            thr = xi + P - Delta
            lo = bisect.bisect_right(xs, thr, 0, M)
            cnt += M - lo
    return 2 * cnt                                 # ordered = 2 * unordered


# ---- arm construction ----
def build_islands(N, M):
    lo = 1 << (N - 1); base = 3 * (1 << (N - 2))
    band_lo, band_hi = lo, 2 * lo
    seen = set(); out = []
    q = 2
    while len(out) < M and q < (lo + 5):
        fl = lo // q
        for d in (base + fl, base - fl):
            if band_lo <= d < band_hi and d not in seen:
                seen.add(d); out.append(d)
                if len(out) >= M:
                    break
        q += 1
    return out


def build_ap(islands, N):
    lo = 1 << (N - 1)
    start = min(islands); span = max(islands) - start
    M = len(islands)
    step = span // (M - 1) if M > 1 else 1
    if step < 1:
        step = 1
    return [start + j * step for j in range(M)]


def null_scalars(N, M, rng):
    lo = 1 << (N - 1)
    return [lo + rng.randrange(lo) for _ in range(M)]


def build_pc2(N, M, c):
    """(M-2c) random curve points + c +- pairs {d_a G, (N-d_a)G} (shared x)."""
    rng = random.Random(999)
    lo = 1 << (N - 1)
    ds = [lo + rng.randrange(lo) for _ in range(M - 2 * c)]
    da = (N_ORD // 3) + 7
    for a in range(c):
        ds.append(da + a); ds.append(N_ORD - (da + a))
    return ds


def pval(stat_arm, stat_nulls):
    B = len(stat_nulls)
    ge = sum(1 for s in stat_nulls if s >= stat_arm)
    return (1 + ge, B + 1)   # exact rational numerator/denominator


def fires(pv):
    num, den = pv
    # p_MC = num/den <= 5/1200 ?
    return num * ALPHA[1] <= ALPHA[0] * den


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 1024
    B = int(sys.argv[3]) if len(sys.argv) > 3 else 999
    Delta = -(-P // M)  # ceil(P/M)
    print(f"# islands curve-image joint-set test | N={N} M={M} B={B} Delta=ceil(P/M)")
    print(f"# baseline 2M^2-M = {2*M*M - M}")

    islands = build_islands(N, M)
    ap = build_ap(islands, N)
    assert len(islands) == M, f"islands short: {len(islands)}"
    rng = random.Random(20260721)

    # curve images
    print("# mapping islands, AP through d*G ...", flush=True)
    Pi = points_affine(islands)
    Pa = points_affine(ap)
    Xi = [x for x, y in Pi]; Yi = [y for x, y in Pi]
    Xa = [x for x, y in Pa]; Ya = [y for x, y in Pa]

    # arm statistics
    s1_isl = add_energy(Xi); s2_isl, z_isl = mul_energy(Xi); s3_isl = add_energy(Yi)
    s4_isl = window_count(Xi, Delta)
    s0_isl = add_energy(islands, mod=N_ORD)            # tautological control
    s1_ap = add_energy(Xa); s4_ap = window_count(Xa, Delta)
    s0_ap = add_energy(ap, mod=N_ORD)

    # nulls
    print(f"# generating {B} Null-B point-sets ...", flush=True)
    s1_n = []; s2_n = []; s3_n = []; s4_n = []; s0_n = []
    for b in range(B):
        ds = null_scalars(N, M, rng)
        Pn = points_affine(ds)
        Xn = [x for x, y in Pn]; Yn = [y for x, y in Pn]
        s1_n.append(add_energy(Xn))
        s2_n.append(mul_energy(Xn)[0])
        s3_n.append(add_energy(Yn))
        s4_n.append(window_count(Xn, Delta))
        s0_n.append(add_energy(ds, mod=N_ORD))
        if (b + 1) % 100 == 0:
            print(f"#   null {b+1}/{B}", flush=True)

    # planted positives (residue-only PC3/PC4 cheap; PC2 curve)
    pc3 = [(1 + 2 * j) % P for j in range(M)]           # residue AP
    pc4 = [pow(3, j, P) for j in range(M)]              # residue GP
    s1_pc3 = add_energy(pc3); s2_pc4 = mul_energy(pc4)[0]
    Ppc2 = points_affine(build_pc2(N, M, 1))
    s1_pc2 = add_energy([x for x, y in Ppc2])

    def show(name, arm, nulls, ap_val=None):
        pv = pval(arm, nulls)
        base = 2 * M * M - M
        tag = "FIRES" if fires(pv) else "null"
        extra = f"  AP={ap_val}({'FIRES' if ap_val is not None and fires(pval(ap_val,nulls)) else 'null'})" if ap_val is not None else ""
        print(f"  {name:5s} arm={arm}  (excess {arm-base:+d})  null[min={min(nulls)},max={max(nulls)}]"
              f"  p_MC={pv[0]}/{pv[1]}  -> {tag}{extra}")

    print("\n=== RESULTS (islands vs Null-B) ===")
    show("S1", s1_isl, s1_n, s1_ap)
    show("S2", s2_isl, s2_n)
    show("S3", s3_isl, s3_n)
    show("S4", s4_isl, s4_n, s4_ap)
    print(f"  S0    islands={s0_isl} AP={s0_ap} null[min={min(s0_n)},max={max(s0_n)}] "
          f"(CONTROL, tautological; islands/AP should exceed nulls)")
    print(f"\n=== PLANTED POSITIVES (must fire) ===")
    print(f"  PC-2 (curve +-pair, S1): {s1_pc2}  excess {s1_pc2-(2*M*M-M):+d}  "
          f"p_MC={pval(s1_pc2,s1_n)}  -> {'FIRES' if fires(pval(s1_pc2,s1_n)) else 'FAIL'}")
    print(f"  PC-3 (residue AP,  S1): {s1_pc3}  excess {s1_pc3-(2*M*M-M):+d}  "
          f"p_MC={pval(s1_pc3,s1_n)}  -> {'FIRES' if fires(pval(s1_pc3,s1_n)) else 'FAIL'}")
    print(f"  PC-4 (residue GP,  S2): {s2_pc4}  excess {s2_pc4-(2*M*M-M):+d}  "
          f"p_MC={pval(s2_pc4,s2_n)}  -> {'FIRES' if fires(pval(s2_pc4,s2_n)) else 'FAIL'}")
    z_note = f"  (islands x=0 count: {z_isl})" if z_isl else ""
    print(f"\n# primary cell = S1 @ N=128,M=1024. alpha*=5/1200.{z_note}")


if __name__ == "__main__":
    main()
