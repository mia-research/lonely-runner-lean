#!/usr/bin/env python3
"""interval_multireadout_v2.py -- v1 extended on all three axes agreed 2026-07-31.

  (1) larger M      -> detectable single-class excess falls like 1/M
  (2) readouts      -> chi_2, chi_3, chi_6 (ONE exponentiation per pair yields all three)
  (3) difference    -> FIELD  x_i - x_j        AND  GROUP-LAW  x(P_i - P_j)

CONSTRUCTED scalars only. No puzzle keys. No generator pool. Exact integers in the signal path.

Key trick: u = d^((P-1)/6) determines the mu_6 class j, and
    chi_6 class = j ,  chi_3 class = j mod 3 ,  chi_2 class = j mod 2
so all three readouts cost one modular exponentiation per pair.
"""
import random, hashlib, sys, time

P  = 2**256 - 2**32 - 977
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
E6 = (P - 1) // 6

# ---- sixth roots of unity, and the class lookup -------------------------------
def _zeta6():
    g = 3
    while pow(g, (P - 1) // 2, P) == 1 or pow(g, (P - 1) // 3, P) == 1: g += 1
    z = pow(g, E6, P)
    tab = {}
    v = 1
    for j in range(6):
        tab[v] = j; v = v * z % P
    assert len(tab) == 6 and v == 1
    return z, tab
ZETA6, Z6TAB = _zeta6()
BETA = pow(2, (P - 1) // 3, P)
assert pow(BETA, 3, P) == 1 and BETA != 1

def mu6_class(d):
    d %= P
    if d == 0: return None
    return Z6TAB[pow(d, E6, P)]

# ---- Jacobian group law + batch inversion ------------------------------------
def jdbl(A):
    X, Y, Z = A
    if Y == 0 or Z == 0: return (0, 0, 0)
    Asq = X * X % P; B = Y * Y % P; C = B * B % P
    D = 2 * ((X + B) * (X + B) - Asq - C) % P
    E = 3 * Asq % P; F = E * E % P
    X3 = (F - 2 * D) % P
    return (X3, (E * (D - X3) - 8 * C) % P, 2 * Y * Z % P)

def jadd(A, B):
    X1, Y1, Z1 = A
    if Z1 == 0: return B
    X2, Y2, Z2 = B
    if Z2 == 0: return A
    Z1Z1 = Z1 * Z1 % P; Z2Z2 = Z2 * Z2 % P
    U1 = X1 * Z2Z2 % P; U2 = X2 * Z1Z1 % P
    S1 = Y1 * Z2 % P * Z2Z2 % P; S2 = Y2 * Z1 % P * Z1Z1 % P
    H = (U2 - U1) % P; r = 2 * (S2 - S1) % P
    if H == 0: return jdbl(A) if r == 0 else (0, 0, 0)
    I = 2 * H % P; I = I * I % P
    J = H * I % P; V = U1 * I % P
    X3 = (r * r - J - 2 * V) % P
    return (X3, (r * (V - X3) - 2 * S1 * J) % P,
            ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) * H % P)

def jneg(A): return (A[0], (-A[1]) % P, A[2])

def jmul(k, Pt=(GX, GY, 1)):
    R = (0, 0, 0); Q = Pt
    while k:
        if k & 1: R = jadd(R, Q)
        Q = jdbl(Q); k >>= 1
    return R

def batch_x(pts):
    """affine x for a list of Jacobian points, ONE inversion total (Montgomery)."""
    zs = [p[2] for p in pts]
    pre = [1] * (len(zs) + 1)
    for i, z in enumerate(zs): pre[i + 1] = pre[i] * z % P
    inv = pow(pre[-1], P - 2, P)
    out = []
    for i in range(len(zs) - 1, -1, -1):
        zi = inv * pre[i] % P
        inv = inv * zs[i] % P
        out.append(pts[i][0] * zi % P * zi % P)
    return out[::-1]

# ---- statistics ---------------------------------------------------------------
def stats(classes):
    """classes: list of mu_6 classes (0..5) of the differences.
       returns exact-integer E2, E3, E6."""
    c = [0] * 6
    for j in classes: c[j] += 1
    a2 = sum(c[j] for j in (0, 2, 4)); b2 = sum(c[j] for j in (1, 3, 5))
    E2 = (a2 - b2) ** 2
    t = [c[0] + c[3], c[1] + c[4], c[2] + c[5]]
    E3 = ((2 * t[0] - t[1] - t[2]) ** 2 + 3 * (t[1] - t[2]) ** 2) // 4
    re = 2 * c[0] + c[1] - c[2] - 2 * c[3] - c[4] + c[5]
    im = c[1] + c[2] - c[4] - c[5]
    E6 = (re * re + 3 * im * im) // 4
    return E2, E3, E6

def field_classes(xs):
    out = []
    n = len(xs)
    for i in range(n):
        xi = xs[i]
        for j in range(i + 1, n):
            v = mu6_class(xi - xs[j])
            if v is not None: out.append(v)
    return out

def group_classes(pts):
    diffs = []
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            d = jadd(pts[i], jneg(pts[j]))
            if d[2] != 0: diffs.append(d)
    xs = batch_x(diffs)
    return [v for v in (mu6_class(x) for x in xs) if v is not None]

# ---- point sources ------------------------------------------------------------
def interval_pts(k, M, rng):
    lo, hi = (1, N) if k >= 256 else (2**(k - 1), 2**k)
    return [jmul(rng.randrange(lo, hi)) for _ in range(M)]

def pool_pts(size, rng):
    """uniform random points of E(F_P); cofactor 1 => uniform group elements. No scalar mult."""
    out = []
    while len(out) < size:
        x = rng.randrange(0, P)
        r = (x * x % P * x + 7) % P
        if pow(r, (P - 1) // 2, P) != 1: continue
        out.append((x, pow(r, (P + 1) // 4, P), 1))
    return out

def glv_closed(M, rng, pool):
    out = []
    for (x, y, _) in pool:
        if len(out) + 3 > M: break
        out += [(x, y, 1), (BETA * x % P, y, 1), (BETA * BETA % P * x % P, y, 1)]
    return out

def plant(M, rng, pool, target=0, cand=1200, scan=150):
    """bias the DIFFERENCE set (v1's plant biased the x-set and did not fire)."""
    cs = rng.sample(pool, min(cand, len(pool)))
    out = [cs.pop()]
    while len(out) < M and cs:
        bi, bh = 0, -1
        for i, q in enumerate(cs[:scan]):
            h = sum(1 for z in out if mu6_class(q[0] - z[0]) == target)
            if h > bh: bi, bh = i, h
        out.append(cs.pop(bi))
    return out

# ---- driver -------------------------------------------------------------------
def null_dist(pool, R, M, rng, mode):
    idx = list(range(len(pool)))
    out = []
    for _ in range(R):
        s = rng.sample(idx, M)
        pts = [pool[i] for i in s]
        cl = field_classes([p[0] for p in pts]) if mode == "field" else group_classes(pts)
        out.append(stats(cl))
    return out

def run(mode, M, R, POOLN, rng, label):
    t0 = time.time()
    print(f"\n{'='*78}\n{label}   M={M}  R={R}  pool={POOLN}\n{'='*78}", flush=True)
    pool = pool_pts(POOLN, rng)
    nulls = null_dist(pool, R, M, rng, mode)
    cols = list(zip(*nulls))
    q = {}
    for i, nm in enumerate(("E2", "E3", "E6")):
        s = sorted(cols[i]); q[nm] = (s, s[int(.95 * R)], s[int(.99 * R)])
        print(f"  null {nm}: median={s[R//2]}  95th={s[int(.95*R)]}  99th={s[int(.99*R)]}")
    def pct(nm, v):
        s = q[nm][0]; return 100.0 * sum(1 for z in s if z < v) / len(s)
    def readout(pts):
        cl = field_classes([p[0] for p in pts]) if mode == "field" else group_classes(pts)
        return stats(cl), len(cl)

    print("  -- controls --")
    (e, npair) = readout(plant(M, rng, pool))
    pl = all(e[i] >= q[nm][2] for i, nm in enumerate(("E3",))[:1]) or e[1] >= q["E3"][2]
    print(f"   C-PLANT  E2={e[0]} ({pct('E2',e[0]):.1f})  E3={e[1]} ({pct('E3',e[1]):.1f})  "
          f"E6={e[2]} ({pct('E6',e[2]):.1f})  -> {'FIRES' if pl else '*** NO FIRE ***'}")
    (e, _) = readout(glv_closed(M, rng, pool))
    print(f"   C-GLV    E2={e[0]}  E3={e[1]}  E6={e[2]}   (E3,E6 forced to 0 on beta-closed sets)")
    glv_ok = (e[1] == 0)
    (e, _) = readout(interval_pts(256, M, rng))
    ng = all(e[i] < q[nm][1] for i, nm in enumerate(("E2", "E3", "E6")))
    print(f"   C-NEG    E2={e[0]} ({pct('E2',e[0]):.1f})  E3={e[1]} ({pct('E3',e[1]):.1f})  "
          f"E6={e[2]} ({pct('E6',e[2]):.1f})  -> {'quiet' if ng else '*** FIRES -- VOID ***'}")
    if not (pl and glv_ok and ng):
        print("   F-VOID: no arm number is read."); return
    print(f"  -- arms ({npair} pairs each) --")
    print(f"   {'k':>5} | {'E2':>10} {'pct':>6} | {'E3':>10} {'pct':>6} | {'E6':>10} {'pct':>6}")
    for k in (40, 64, 96, 128, 135, 160, 200):
        (e, _) = readout(interval_pts(k, M, rng))
        flags = "".join(" FIRE" if e[i] >= q[nm][2] else "" for i, nm in enumerate(("E2","E3","E6")))
        print(f"   {k:>5} | {e[0]:>10} {pct('E2',e[0]):>5.1f}% | {e[1]:>10} {pct('E3',e[1]):>5.1f}%"
              f" | {e[2]:>10} {pct('E6',e[2]):>5.1f}%{flags}")
    print(f"  [{time.time()-t0:.0f}s]")

if __name__ == "__main__":
    with open("PREREG_interval_cubic_structure_v1.md", "rb") as f:
        print("v1 PREREG SHA-256:", hashlib.sha256(f.read()).hexdigest())
    rng = random.Random(20260731)
    run("field", 400, 600, 1200, rng, "AXIS 1+2 -- FIELD difference x_i - x_j, readouts chi_2/chi_3/chi_6")
    run("group", 160, 300,  600, rng, "AXIS 3   -- GROUP-LAW difference x(P_i - P_j)  [CM-native]")
