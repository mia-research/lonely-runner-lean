#!/usr/bin/env python3
"""
difference_set_xy_geometry_v1.py -- objects (2)+(3): the difference-set DISTRIBUTION geometry with
the xy odd+mu3 harmonic (rigidity governs exact chaining, NOT distributional structure -> genuinely new).

Extends bilinear_jointset_harness's difference-set cubic moment (Sum_pairs eis(x(P_i-P_j))^3) with:
  * mu3 resonance of the difference set:      M3   = Sum chi3(x(P_i-P_j))
  * xy odd+mu3 harmonic moment:               M3xy = Sum chi3(xy(P_i-P_j)),  xy=X*Y
  * eis cubic moment (baseline, harness):     |Sum eis(x_diff)^3|
Normalized |M|/sqrt(#pairs): ~1 for a random set (root-N fluctuation), >>1 for additive structure.

CONTROLS (must fire): arithmetic progression (AP: d0+i*delta -> difference set = {i*delta}, strongly
structured) and a GLV-triple set (keys closed under d->lambda*d -> mu3 resonance). Random-curve = null.
Sets: constructed 36k (known generator), real 82, AP, GLV, random.  Exact int; magnitudes analytic-size.
"""
import csv, cmath, math, random
from ecc_secp256k1 import P as FP, N_ORDER, scalar_mul
from int1_frame_operator_v1 import build
eis, eps = build(FP)
Z3 = cmath.exp(2j*math.pi/3)


def add_affine(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2:
        if (y1+y2) % FP == 0: return None
        lam = (3*x1*x1) * pow(2*y1, -1, FP) % FP
    else:
        lam = (y2-y1) * pow(x2-x1, -1, FP) % FP
    x3 = (lam*lam - x1 - x2) % FP
    return x3, (lam*(x1-x3)-y1) % FP

def neg(A): return (A[0], (-A[1]) % FP)
def emul(z, w):
    a, b = z; c, d = w
    return (a*c-b*d, a*d+b*c-b*d)
def ecube(z): return emul(emul(z, z), z)
def enorm(z): a, b = z; return a*a-a*b+b*b

_cbexp = (FP-1)//3
def chi3(a):
    a %= FP
    if a == 0: return 0.0+0j
    r = pow(a, _cbexp, FP)              # in {1, w, w^2}
    if r == 1: return 1.0+0j
    # map the two nontrivial cube roots of 1 to Z3, Z3^2 by a fixed convention (smaller->Z3)
    r2 = pow(r, 2, FP)
    return Z3 if r < r2 else Z3*Z3

def moments(points, maxpairs=12000, seed=0):
    rng = random.Random(seed)
    npt = len(points)
    pairs = [(i, j) for i in range(npt) for j in range(i+1, npt)]
    if len(pairs) > maxpairs:
        pairs = rng.sample(pairs, maxpairs)
    cs = [0, 0]; M3 = 0j; M3xy = 0j; cnt = 0
    for i, j in pairs:
        diff = add_affine(points[i], neg(points[j]))
        if diff is None: continue
        xd, yd = diff
        c = ecube(eis(xd)); cs[0] += c[0]; cs[1] += c[1]
        M3 += chi3(xd)
        M3xy += chi3((xd*yd) % FP)
        cnt += 1
    s = math.sqrt(cnt) if cnt else 1
    return dict(n=cnt, eis_cube=math.sqrt(enorm(cs))/s, M3=abs(M3)/s, M3xy=abs(M3xy)/s)


def main():
    print("="*78)
    print("DIFFERENCE-SET geometry with the xy/mu3 harmonic  (|M|/sqrt(pairs): ~1 random, >>1 structured)")
    print("="*78)
    random.seed(1)
    SZ = 160
    # constructed 36k (known generator)
    con = []
    with open("constructed_keys_fullrange_v1.csv") as f:
        for r in csv.DictReader(f):
            con.append((int(r["X"], 16), int(r["Y"], 16)))
            if len(con) >= 4000: break
    constructed = random.sample(con, SZ)
    # real 82
    real = []
    with open("solved_keys_augmented_v1.csv") as f:
        for r in csv.DictReader(f):
            real.append((int(r["X"], 16), int(r["Y"], 16)))
    # random curve points (null)
    randset = [scalar_mul(random.randrange(1, N_ORDER)) for _ in range(SZ)]
    # AP control (must fire)
    d0 = random.randrange(1, N_ORDER); delta = random.randrange(1, 1 << 40)
    apset = [scalar_mul((d0 + i*delta) % N_ORDER) for i in range(SZ)]
    # GLV-triple control (mu3 resonance): keys closed under d->lambda d
    lam = pow(2, (N_ORDER-1)//3, N_ORDER)
    if pow(lam, 3, N_ORDER) != 1:
        lam = [l for l in range(2, 10000) if pow(l, 3, N_ORDER) == 1 and l != 1][0]
    glvset = []
    for _ in range(SZ//3):
        dd = random.randrange(1, N_ORDER)
        glvset += [scalar_mul(dd), scalar_mul(dd*lam % N_ORDER), scalar_mul(dd*lam*lam % N_ORDER)]

    for name, pts in [("random-curve (NULL)", randset), ("constructed-36k", constructed),
                      ("real-82", real), ("AP control (fires)", apset),
                      ("GLV-triple control", glvset)]:
        m = moments(pts)
        print("  %-22s n_pairs=%-6d  eis-cube=%6.2f  M3(mu3-x)=%6.2f  M3xy(mu3-xy)=%6.2f"
              % (name, m["n"], m["eis_cube"], m["M3"], m["M3xy"]))
    print("\n READ: random ~1. If AP/GLV controls spike (>>1) and real/constructed ~ random => no")
    print("       difference-set geometry in the real keys beyond generic (with the xy-harmonic too).")
    print("[done]")


if __name__ == '__main__':
    main()
