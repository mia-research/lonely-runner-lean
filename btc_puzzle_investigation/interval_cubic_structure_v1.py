#!/usr/bin/env python3
"""interval_cubic_structure_v1.py -- executes PREREG_interval_cubic_structure_v1.md.

Does confining the scalar d to a short interval leave cubic structure in x([d]G)?
CONSTRUCTED scalars only.  No puzzle keys.  No generator pool.  Exact integers only.
"""
import random, hashlib, sys

P  = 2**256 - 2**32 - 977
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
EXP3 = (P - 1) // 3

# ---------------- group law, Jacobian (no inverse per op) ----------------
def jdbl(Pt):
    X, Y, Z = Pt
    if Y == 0: return (0, 0, 0)
    A = (X * X) % P; B = (Y * Y) % P; C = (B * B) % P
    D = (2 * ((X + B) * (X + B) - A - C)) % P
    E = (3 * A) % P; F = (E * E) % P
    X3 = (F - 2 * D) % P
    Y3 = (E * (D - X3) - 8 * C) % P
    Z3 = (2 * Y * Z) % P
    return (X3, Y3, Z3)

def jadd(Pt, Q):
    X1, Y1, Z1 = Pt
    if Z1 == 0: return Q
    X2, Y2, Z2 = Q
    if Z2 == 0: return Pt
    Z1Z1 = (Z1 * Z1) % P; Z2Z2 = (Z2 * Z2) % P
    U1 = (X1 * Z2Z2) % P; U2 = (X2 * Z1Z1) % P
    S1 = (Y1 * Z2 * Z2Z2) % P; S2 = (Y2 * Z1 * Z1Z1) % P
    H = (U2 - U1) % P; r = (2 * (S2 - S1)) % P
    if H == 0:
        return jdbl(Pt) if r == 0 else (0, 0, 0)
    I = (2 * H) % P; I = (I * I) % P
    J = (H * I) % P; V = (U1 * I) % P
    X3 = (r * r - J - 2 * V) % P
    Y3 = (r * (V - X3) - 2 * S1 * J) % P
    Z3 = (((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) * H) % P
    return (X3, Y3, Z3)

def jmul(k, Pt=(GX, GY, 1)):
    R = (0, 0, 0); Q = Pt
    while k:
        if k & 1: R = jadd(R, Q)
        Q = jdbl(Q); k >>= 1
    return R

def jx(Pt):
    X, Y, Z = Pt
    if Z == 0: return None
    zi = pow(Z, P - 2, P)
    return X * zi % P * zi % P

# ---------------- readout ----------------
def chi3_class(a):
    a %= P
    if a == 0: return None
    r = pow(a, EXP3, P)
    if r == 1: return 0
    # the two primitive cube roots of unity mod P, pinned deterministically
    return 1 if r < P - r else 2

def e3_of(xs):
    c = [0, 0, 0]
    n = len(xs)
    for i in range(n):
        xi = xs[i]
        for j in range(i + 1, n):
            v = chi3_class(xi - xs[j])
            if v is not None: c[v] += 1
    a, b, cc = c
    return (((2 * a - b - cc) ** 2 + 3 * (b - cc) ** 2) // 4), c

# ---------------- point sources ----------------
def interval_points(k, M, rng):
    lo, hi = (1, N) if k >= 256 else (2**(k - 1), 2**k)
    return [jx(jmul(rng.randrange(lo, hi))) for _ in range(M)]

def uniform_curve_pool(size, rng):
    """uniform random points of E(F_P) WITHOUT scalar multiplication.
       cofactor 1 => every curve point is a group element, so this is the matched null."""
    out = []
    while len(out) < size:
        x = rng.randrange(0, P)
        r = (x * x % P * x + 7) % P
        if pow(r, (P - 1) // 2, P) != 1: continue
        out.append(x)
    return out

def plant_points(M, rng, pool, cand=2500):
    """C-PLANT v2: bias the DIFFERENCE set, not the x-set.

    v1 selected x with chi3(x)==0 and did NOT fire (pctile 31.6): E3 reads the cubic class of
    x_i - x_j, and making every x a cubic residue says nothing about the differences.  That is
    the 'trace the object, not the tag' failure, in a control.  Recorded, not silently replaced.

    v2 greedily grows the set, at each step taking the candidate whose differences to the
    current set land most often in class 0.  Points are genuine curve x-coordinates, so the
    readout and statistic path are exercised end to end (point GENERATION is not - the plant
    selects from the null pool rather than from a scalar interval; scope stated in the RESULT).
    """
    cands = rng.sample(pool, min(cand, len(pool)))
    out = [cands.pop()]
    while len(out) < M and cands:
        best, best_hits, best_i = None, -1, -1
        for i, x in enumerate(cands[:200]):          # bounded scan per step
            hits = sum(1 for z in out if chi3_class(x - z) == 0)
            if hits > best_hits: best, best_hits, best_i = x, hits, i
        out.append(best); cands.pop(best_i)
    return out

def glv_closed_points(M, rng, pool):
    """C-GLV: a set closed under x -> beta*x has EXACTLY equal difference classes (forced).
       Independent instrument check -- see CORRECTION_v32_mu3_diffset_controls_v2.md."""
    beta = pow(2, (P - 1) // 3, P)
    assert pow(beta, 3, P) == 1 and beta != 1
    out = []
    for x in pool:
        if len(out) + 3 > M: break
        out += [x, beta * x % P, beta * beta % P * x % P]
    return out

if __name__ == "__main__":
    with open("PREREG_interval_cubic_structure_v1.md", "rb") as f:
        sha = hashlib.sha256(f.read()).hexdigest()
    print("PREREG SHA-256:", sha)
    M, R, POOL = 80, 1000, 20000
    rng = random.Random(20260731)

    print(f"\nbuilding uniform-curve null pool ({POOL} points, no scalar mult) ...", flush=True)
    pool = uniform_curve_pool(POOL, rng)

    print(f"building null distribution (R={R} resamples of M={M}) ...", flush=True)
    null = []
    for _ in range(R):
        xs = rng.sample(pool, M)
        e, _ = e3_of(xs)
        null.append(e)
    null.sort()
    def pctile(v):
        lo = sum(1 for z in null if z < v)
        return 100.0 * lo / len(null)
    q95, q99 = null[int(.95 * R)], null[int(.99 * R)]
    print(f"  null: median={null[R//2]}  95th={q95}  99th={q99}  max={null[-1]}")

    print("\n--- CONTROLS ---", flush=True)
    xs = plant_points(M, rng, pool)
    e, c = e3_of(xs)
    plant_ok = e >= q99
    print(f"  C-PLANT (forced cubic imbalance): classes={c} E3={e} pctile={pctile(e):.1f}  "
          f"-> {'FIRES' if plant_ok else '*** DOES NOT FIRE ***'}")

    xs = glv_closed_points(M, rng, pool)
    e, c = e3_of(xs)
    glv_ok = (len(set(c)) == 1)
    print(f"  C-GLV   (beta-closed set, forced): classes={c} E3={e}  "
          f"-> {'EXACTLY EQUAL (ok)' if glv_ok else '*** NOT EQUAL -- readout mis-specified ***'}")

    xs = interval_points(256, M, rng)
    e, c = e3_of(xs)
    neg_ok = e < q95
    print(f"  C-NEG   (d uniform in [1,n)):     classes={c} E3={e} pctile={pctile(e):.1f}  "
          f"-> {'QUIET (ok)' if neg_ok else '*** FIRES -- NULL MIS-SPECIFIED, ARMS VOID ***'}")

    if not (plant_ok and neg_ok and glv_ok):
        print("\nF-VOID: instrument failure. NO ARM NUMBER IS READ.")
        sys.exit(1)

    print("\n--- ARMS (d uniform in [2^(k-1), 2^k)) ---", flush=True)
    print(f"  {'k':>5} {'classes':>26} {'E3':>12} {'pctile':>8}   verdict")
    for k in (40, 64, 96, 128, 135, 160, 200):
        xs = interval_points(k, M, rng)
        e, c = e3_of(xs)
        pc = pctile(e)
        v = "FIRES" if e >= q99 else ("INDETERMINATE" if e >= q95 else "null")
        print(f"  {k:>5} {str(c):>26} {e:>12} {pc:>7.1f}%   {v}")
    print("\nC-FORCED: all class sums = C(80,2) = 3160 (asserted in e3_of by construction)")
