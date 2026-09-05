#!/usr/bin/env python3
"""
mu3_projection_v1.py -- execute PREREG_mu3_orthogonal_projection_v1.md, ARM 1 (H_proj) + plants.

Registered hypothesis (NOT the literal projection, which is a forced zero -- section 1.3):
  H_proj: at FIXED #R (fixed ceiling), mu3-isotype content controls the EXTREMAL spectral magnitude.

PRIMARY: D4(u) = S_{chi2(y)}(u) - S_{chi2((x-x1)(x-x2))}(u),   both #R=4, same ceiling 4 sqrt p.
  S_f(u) = mean of the 16 largest Q_f(a)=|V_f(a)|^2/p over a in A_rep (the (n-1)/6 mu6-orbit reps).
Ranked per unit against NULL-A (orbit-value relabel preserving each readout's own symmetry + counts),
combined across units by Stouffer.

EXACTNESS: signal path (c_d in {-1,0,1}, coords) is exact int.  |V(a)|^2 is obtained by numpy FFT of
the integer c-sequence; this is the section-8 monotone-statistic-ranked-against-matched-null carve-out
(DEVIATION D-float: float FFT in place of the certified fixed-point of section 8 -- same pipeline is
applied to every null draw, and the primary is a rank; a top-16 boundary-gap check guards ties).
Usage: mu3_projection_v1.py [n_lo] [n_hi] [M] [per_stratum]
"""
import sys, math, hashlib
import numpy as np

B = 7
K_TOP = 16


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def _arr_legendre(rhs, p):
    """Vectorized Legendre symbols of an int64 array rhs mod p (Euler's criterion by squaring)."""
    e = (p - 1) // 2
    base = rhs % p
    res = np.ones_like(base)
    while e > 0:
        if e & 1:
            res = res * base % p
        base = base * base % p
        e >>= 1
    return np.where(rhs % p == 0, 0, np.where(res == 1, 1, -1))


def count_E(p):
    x = np.arange(p, dtype=np.int64)
    rhs = (x * x % p * x + B) % p
    return p + 1 + int(_arr_legendre(rhs, p).sum())


def is_prime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d = m - 1; r = 0
    while d % 2 == 0:
        d //= 2; r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def cube_root_unity(p):
    # beta of order 3 in F_p^*, p = 1 mod 3
    g = 2
    while pow(g, (p - 1) // 2, p) == 1 or pow(g, (p - 1) // 3, p) == 1:
        g += 1
    return pow(g, (p - 1) // 3, p)


def order3_modn(n):
    # lambda of order 3 in (Z/n)^*, n = 1 mod 3
    g = 2
    while True:
        lam = pow(g, (n - 1) // 3, n)
        if lam != 1 and pow(lam, 3, n) == 1:
            return lam
        g += 1


def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        m = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
    else:
        m = (y2 - y1) * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (m * m - x1 - x2) % p
    return (x3, (m * (x1 - x3) - y1) % p)


def find_generator(p, n):
    for x0 in range(1, p):
        rhs = (x0 * x0 % p * x0 + B) % p
        if rhs == 0 or pow(rhs, (p - 1) // 2, p) != 1:
            continue
        y0 = pow(rhs, (p + 1) // 4, p) if p % 4 == 3 else tonelli(rhs, p)
        y0 = min(y0, p - y0)
        G = (x0, y0)
        # n prime => any non-O point generates
        return G
    raise RuntimeError("no generator")


def tonelli(a, p):
    a %= p
    if pow(a, (p - 1) // 2, p) != 1:
        raise ValueError
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q = p - 1; s = 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m = s; c = pow(z, q, p); t = pow(a, q, p); r = pow(a, (q + 1) // 2, p)
    while t != 1:
        i = 0; tt = t
        while tt != 1:
            tt = tt * tt % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m = i; c = b * b % p; t = t * c % p; r = r * b % p
    return r


def coords(G, p, n):
    xs = [0] * n; ys = [0] * n
    P = G
    for d in range(1, n):
        xs[d] = P[0]; ys[d] = P[1]
        P = ec_add(P, G, p)
    return xs, ys


def mu6_reps(n, lam):
    seen = [False] * n
    reps = []
    for a in range(1, n):
        if seen[a]:
            continue
        orb = set()
        t = a
        for _ in range(3):
            orb.add(t); orb.add((n - t) % n)
            t = t * lam % n
        for o in orb:
            seen[o] = True
        reps.append(min(orb))
    return reps


def readout(kind, xs, ys, p, x0=None, x1=None, x2=None):
    x = np.asarray(xs, dtype=np.int64); y = np.asarray(ys, dtype=np.int64)
    if kind == 'y':
        v = y
    elif kind == 'x':
        v = x
    elif kind == 'xy':
        v = x * y % p
    elif kind == 'x_x0':
        v = (x - x0) % p
    elif kind == 'gx1x2':
        v = (x - x1) * (x - x2) % p
    elif kind == 'y_x_x0':
        v = y * (x - x0) % p
    c = _arr_legendre(v % p, p)
    c[0] = 0                                   # d=0 is the identity O, excluded
    return c.astype(np.int64)


def Q_at(c, reps):
    V = np.fft.fft(c.astype(float))
    Q = (V.real ** 2 + V.imag ** 2)
    return Q[reps]


def S_top(Qreps, k=K_TOP):
    idx = np.argpartition(Qreps, -k)[-k:]
    return float(np.mean(Qreps[idx])), Qreps[idx]


def orbit_partition(n, lam, mu3):
    """Return list of orbits (each an ordered tuple) under mu6 if mu3 else mu2."""
    seen = [False] * n
    orbits = []
    for a in range(1, n):
        if seen[a]:
            continue
        if mu3:
            elems = []
            t = a
            for _ in range(3):
                elems.append(t); elems.append((n - t) % n)
                t = t * lam % n
            # dedupe preserving order
            uniq = []
            for e in elems:
                if e not in uniq:
                    uniq.append(e)
        else:
            uniq = [a, (n - a) % n]
            if uniq[1] == uniq[0]:
                uniq = [a]
        for e in uniq:
            seen[e] = True
        orbits.append(tuple(uniq))
    return orbits


def null_S(c, orbits, reps, M, rng, k=K_TOP):
    """NULL-A: relabel whole orbits (preserve within-orbit position) -> preserves symmetry+counts."""
    n = len(c)
    # canonical per-orbit value blocks
    sizes = np.array([len(o) for o in orbits])
    uniform = len(set(sizes.tolist())) == 1
    reps = np.asarray(reps)
    out = np.empty(M)
    if uniform:
        L = int(sizes[0])
        base = np.array([list(o) for o in orbits], dtype=np.int64)   # (O, L)
        vals = c[base]                                                # (O, L) real values per orbit
        O = base.shape[0]
        for m in range(M):
            perm = rng.permutation(O)
            cc = np.zeros(n, dtype=np.int64)
            cc[base] = vals[perm]                                     # move whole orbits
            out[m], _ = S_top(Q_at(cc, reps), k)
    else:
        for m in range(M):
            perm = rng.permutation(len(orbits))
            cc = np.zeros(n, dtype=np.int64)
            for i, o in enumerate(orbits):
                src = orbits[perm[i]]
                for pos, e in enumerate(o):
                    cc[e] = c[src[pos % len(src)]]
            out[m], _ = S_top(Q_at(cc, reps), k)
    return out


def stratum(p):
    cr = pow(B, (p - 1) // 3, p)          # cubic residue test of B
    if p % 4 == 1:
        return 'S1'
    return 'S2' if cr == 1 else 'S3'


def find_units(n_lo, n_hi, per_stratum, p_min=0):
    got = {'S1': [], 'S2': [], 'S3': []}
    p = max(3001, p_min)
    if p % 2 == 0:
        p += 1
    while min(len(v) for v in got.values()) < per_stratum:
        if is_prime(p) and p % 3 == 1:
            n = count_E(p)
            if n_lo <= n <= n_hi and is_prime(n):
                s = stratum(p)
                if len(got[s]) < per_stratum:
                    got[s].append((p, n))
        p += 2
        if p > 20 * n_hi:
            break
    return got


def run_unit(p, n, M, rng, verbose=True):
    beta = cube_root_unity(p)
    lam = order3_modn(n)
    G = find_generator(p, n)
    xs, ys = coords(G, p, n)
    reps = mu6_reps(n, lam)
    assert len(reps) == (n - 1) // 6, (len(reps), (n - 1) // 6)
    # frozen readout parameters
    x0 = next(v for v in range(1, p) if (v * v % p * v + B) % p != 0)
    pairs = [(a, b) for a in range(1, p) for b in range(a + 1, p)]
    x1, x2 = next((a, b) for a, b in pairs
                  if (a*a%p*a+B) % p != 0 and (b*b%p*b+B) % p != 0
                  and {a % p, b % p} != {beta*a % p, beta*b % p})
    cy = readout('y', xs, ys, p)
    cg = readout('gx1x2', xs, ys, p, x1=x1, x2=x2)
    # section 2.4 exact l2 identity
    for c in (cy, cg):
        lhs = int((np.abs(np.fft.fft(c.astype(float))) ** 2).sum().round())
        rhs = n * int(np.count_nonzero(c))
        assert abs(lhs - rhs) <= 3, (lhs, rhs)
    Sy, topy = S_top(Q_at(cy, reps))
    Sg, topg = S_top(Q_at(cg, reps))
    D4 = Sy - Sg
    # top-16 boundary-gap guard (float-tie check)
    gapy = float(np.sort(Q_at(cy, reps))[-K_TOP] - np.sort(Q_at(cy, reps))[-K_TOP-1])
    orb6 = orbit_partition(n, lam, mu3=True)
    orb2 = orbit_partition(n, lam, mu3=False)
    Sy_null = null_S(cy, orb6, reps, M, rng)
    Sg_null = null_S(cg, orb2, reps, M, rng)
    D4_null = Sy_null - Sg_null
    ge = int(np.count_nonzero(D4_null >= D4))
    le = int(np.count_nonzero(D4_null <= D4))
    p_lo = (1 + le) / (M + 1)
    p_hi = (1 + ge) / (M + 1)
    if verbose:
        print("  p=%-6d n=%-6d %s  Sy=%.3f Sg=%.3f | Sy_null=%.3f Sg_null=%.3f  D4=%+.4f  Dnull mean=%+.4f sd=%.4f  p_lo=%.4f  gap=%.1f"
              % (p, n, stratum(p), Sy/p, Sg/p, Sy_null.mean()/p, Sg_null.mean()/p,
                 D4/p, D4_null.mean()/p, D4_null.std()/p, p_lo, gapy))
    return dict(p=p, n=n, strat=stratum(p), Sy=Sy, Sg=Sg, D4=D4,
                Sy_null=float(Sy_null.mean()), Sg_null=float(Sg_null.mean()),
                nullmean=float(D4_null.mean()), nullsd=float(D4_null.std()),
                p_lo=p_lo, p_hi=p_hi)


def stouffer(pvals):
    from statistics import NormalDist
    nd = NormalDist()
    zs = [nd.inv_cdf(max(min(1 - pv, 1 - 1e-12), 1e-12)) for pv in pvals]
    return sum(zs) / math.sqrt(len(zs))


# ------------------------------------------------------- PLANTS
def plant_P1(n, reps, rng):
    """rank ladder: r frequencies at EQUAL fixed magnitude -> top-16 mean S must increase in r.
    (Deviation P1-real: planted sequences are real-valued, not {+-1}, so per-frequency magnitude is
    held fixed -- that is exactly the rank-resolution property under test; the +-1 detail is not.)"""
    print("\n--- P-1 rank ladder (equal-magnitude planted freqs; S must strictly increase in r) ---")
    prev = None; ok = True
    ds = np.arange(n)
    A = 8.0                                    # planted amplitude >> white floor (sd 1)
    for r in (1, 2, 3, 4, 6):
        c = rng.standard_normal(n)             # white background, unit sd
        for j in range(r):
            a = int(reps[(j * 7 + 3) % len(reps)])
            c += A * np.cos(2 * np.pi * a * ds / n + 0.3 * j)
        c[0] = 0.0
        S, _ = S_top(Q_at(c, reps))
        flag = ""
        if prev is not None and S <= prev:
            flag = "  *** NOT increasing ***"; ok = False
        print("    r=%d  S=%.3e%s" % (r, S, flag))
        prev = S
    print("    P-1 %s" % ("ORDERS -> pipeline has rank resolution" if ok else "FAILED -> PIPELINE DEFECT"))
    return ok


def plant_P3(n, lam, reps, rng):
    """planted isotype effect: build mu3-invariant vs non-invariant with heavier top-16 by delta."""
    print("\n--- P-3 planted isotype effect (D4 must detect delta) ---")
    orb6 = orbit_partition(n, lam, mu3=True)
    ds = np.arange(n)
    # invariant carrier: constant on mu6 orbits, spread spectrum
    inv = np.zeros(n, dtype=np.int64)
    for o in orb6:
        v = 1 if rng.random() < 0.5 else -1
        for e in o:
            inv[e] = v
    inv[0] = 0
    base_S, _ = S_top(Q_at(inv, reps))
    detected = None
    for delta in (0.5, 0.2, 0.1, 0.05, 0.02, 0.01):
        # non-invariant: same value counts, plant a concentrated mode of relative size delta
        a = int(reps[5])
        boost = np.sign(np.cos(2 * np.pi * a * ds / n)).astype(np.int64)
        # blend by delta fraction of positions
        noninv = inv.copy()
        kflip = int(delta * n)
        idx = rng.permutation(n)[:kflip]
        noninv[idx] = boost[idx]
        noninv[0] = 0
        Sn, _ = S_top(Q_at(noninv, reps))
        d4 = Sn - base_S
        print("    delta=%.2f  Sn/base=%.3f  D4(planted)/p-scale=%+.2f" % (delta, Sn / base_S, d4 / n))
        if d4 > 0.1 * base_S and detected is None:
            detected = delta
    print("    P-3 detects down to delta = %s" % (detected if detected else ">50%% (FAIL)"))
    return detected


def main():
    n_lo = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    n_hi = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
    M = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    per = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    rng = np.random.default_rng(20260724)
    print("=" * 92)
    print("mu3 PROJECTION -- H_proj  D4 = S_chi2(y) - S_chi2((x-x1)(x-x2))  [both #R=4]  M=%d" % M)
    print("=" * 92)

    print("\n=== finding DISCOVERY units (fresh, per-stratum=%d, n in [%d,%d]) ===" % (per, n_lo, n_hi))
    units = find_units(n_lo, n_hi, per)
    allu = []
    for s in ('S1', 'S2', 'S3'):
        print("  %s: %s" % (s, units[s]))
        allu += units[s]

    print("\n=== PLANTS (on the first unit) ===")
    p0, n0 = allu[0]
    lam0 = order3_modn(n0); reps0 = mu6_reps(n0, lam0)
    pr = np.random.default_rng(1)
    p1_ok = plant_P1(n0, reps0, pr)
    p3_det = plant_P3(n0, lam0, reps0, pr)

    print("\n=== DISCOVERY units ===")
    res = [run_unit(p, n, M, rng) for p, n in allu]

    print("\n=== POOLED ===")
    for tail, key in (("lower (H_proj: S_y < S_g)", 'p_lo'), ("upper", 'p_hi')):
        z = stouffer([r[key] for r in res])
        print("  Stouffer Z (%s) = %+.3f  (|Z|>2.58 = outside alpha=0.01 band)" % (tail, z))
    # sign replication by stratum
    for s in ('S1', 'S2', 'S3'):
        rs = [r for r in res if r['strat'] == s]
        neg = sum(1 for r in rs if r['D4'] < r['nullmean'])
        print("  %s: %d/%d units have D4 below null mean" % (s, neg, len(rs)))
    print("\nMU3_DONE  (P-1 %s, P-3 detects %s)" % ("ok" if p1_ok else "FAIL", p3_det))


if __name__ == '__main__':
    main()
