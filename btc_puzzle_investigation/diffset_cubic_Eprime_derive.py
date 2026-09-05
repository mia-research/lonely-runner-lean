#!/usr/bin/env python3
# Step 2 of PREREG_diffset_cubic_cmvanishing_v1.md
# Derive [d]G' on E': y^2 = x^3 + a'*x + b' (GENERALIZED Weierstrass, a' != 0).
# Uses Jacobian coordinates with a-correct doubling. Exact integer arithmetic (gmpy2).
#
# Generalized Jacobian formulas (a != 0):
#   doubling:   M = 3 X^2 + a Z^4 ;  S = 4 X Y^2 ;  X' = M^2 - 2S ; ...
#   addition:   standard (a-independent)
#
# This produces solved_puzzles_xy_Eprime.csv (82 real d's -> X',Y') and
# constructed_keys_Eprime_100k.csv (100,023 constructed d's -> X',Y').
# NO E3 IS COMPUTED HERE (the null must be frozen first, per prereg).

import csv, json, sys, time
try:
    from gmpy2 import mpz, powmod, invert
    FAST = True
except Exception:
    FAST = False
    def invert(a, m): return pow(a, -1, m)

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"

# Load E' params from the curve-setup meta
with open(f"{BASE}/diffset_cubic_Eprime_meta_v1.json") as f:
    M = json.load(f)
P   = int(M["P"])
AA  = int(M["a"])           # curve coefficient a' (NOT to be confused with secp's a=0)
BB  = int(M["b"])
Np  = int(M["n_prime"])
Gxp = int(M["Gx"])
Gyp = int(M["Gy"])
print(f"E': y^2 = x^3 + {AA}*x + {BB} over P; n' = {Np}  ({Np.bit_length()} bits); G'=({hex(Gxp)[:14]}..., {hex(Gyp)[:14]}...)", flush=True)

# ---- generalized Jacobian arithmetic for y^2 = x^3 + AA*x + BB ----
def jac_dbl(X, Y, Z):
    if Y == 0: return (0, 1, 0)
    # M = 3 X^2 + a Z^4
    ZZ = (Z * Z) % P
    ZZZZ = (ZZ * ZZ) % P
    XX = (X * X) % P
    M_ = (3 * XX + AA * ZZZZ) % P
    # S = 4 X Y^2
    YY = (Y * Y) % P
    S = (4 * X * YY) % P
    X3 = (M_ * M_ - 2 * S) % P
    Y3 = (M_ * (S - X3) - 8 * YY * YY) % P
    Z3 = (2 * Y * Z) % P
    return (X3, Y3, Z3)

def jac_add(P1, P2):
    X1, Y1, Z1 = P1; X2, Y2, Z2 = P2
    if Z1 == 0: return P2
    if Z2 == 0: return P1
    Z1Z1 = (Z1 * Z1) % P
    Z2Z2 = (Z2 * Z2) % P
    U1 = (X1 * Z2Z2) % P
    U2 = (X2 * Z1Z1) % P
    S1 = (Y1 * Z2 * Z2Z2) % P
    S2 = (Y2 * Z1 * Z1Z1) % P
    if U1 == U2:
        if S1 != S2: return (0, 1, 0)
        return jac_dbl(X1, Y1, Z1)
    H = (U2 - U1) % P
    HH = (H * H) % P
    HHH = (H * HH) % P
    r = (S2 - S1) % P
    V = (U1 * HH) % P
    X3 = (r * r - HHH - 2 * V) % P
    Y3 = (r * (V - X3) - S1 * HHH) % P
    Z3 = (Z1 * Z2 * H) % P
    return (X3, Y3, Z3)

def scalar_mul_g(k, base=(Gxp, Gyp)):
    """affine (x,y) = k*base on E', exact."""
    R = (0, 1, 0)
    Q = (base[0], base[1], 1)
    while k > 0:
        if k & 1: R = jac_add(R, Q)
        Q = jac_dbl(*Q)
        k >>= 1
    Xx, Yy, Zz = R
    if Zz == 0: return None
    zi = pow(Zz, P - 2, P)
    zi2 = (zi * zi) % P
    return ((Xx * zi2) % P, (Yy * zi2 * zi) % P)

# ---- self-test: verify [n']G' = O (generator order) ----
G_jac = (Gxp, Gyp, 1)
# compute [n']G via repeated doubling+add on the affine base
O_check = scalar_mul_g(Np)
print(f"self-test [n']G' = O: {'PASS' if O_check is None else 'FAIL'}", flush=True)
assert O_check is None, "[n']G' != O -- curve meta is wrong"

# also: G' is on E'
lhs = (Gyp * Gyp) % P
rhs = (Gxp*Gxp*Gxp + AA*Gxp + BB) % P
assert lhs == rhs, "G' not on E'"
print("self-test G' on E': PASS", flush=True)

# ============ REAL 82 on E' ============
print(f"\n=== REAL 82 on E' ===", flush=True)
real_rows = []
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    rdr = csv.DictReader(f)
    fieldnames = rdr.fieldnames + ["X_Eprime", "Y_Eprime"]
    for r in rdr:
        d = int(r["private_key"], 16)
        xy = scalar_mul_g(d)
        assert xy is not None, f"d={d} gave identity (d multiple of n'?)"
        r2 = dict(r); r2["X_Eprime"] = hex(xy[0])[2:]; r2["Y_Eprime"] = hex(xy[1])[2:]
        real_rows.append(r2)
print(f"derived {len(real_rows)} real [d]G' on E'", flush=True)
assert len(real_rows) == 82, f"expected 82 real, got {len(real_rows)}"

out_real = f"{BASE}/solved_puzzles_xy_Eprime.csv"
with open(out_real, "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=fieldnames)
    w.writeheader()
    for r in real_rows: w.writerow(r)
print(f"wrote {out_real}", flush=True)

# ============ 100k CONSTRUCTED on E' (cache; ~3-5 min) ============
print(f"\n=== 100k constructed pool on E' (this takes a few minutes) ===", flush=True)
t0 = time.time()
n_done = 0
with open(f"{BASE}/constructed_keys_1to160_100k.csv") as fin:
    rdr = csv.DictReader(fin)
    fieldnames_c = rdr.fieldnames + ["X_Eprime", "Y_Eprime"]
    out_c = f"{BASE}/constructed_keys_Eprime_100k.csv"
    with open(out_c, "w", newline="") as fout:
        w = csv.DictWriter(fout, fieldnames=fieldnames_c)
        w.writeheader()
        for r in rdr:
            d = int(r["d"])
            xy = scalar_mul_g(d)
            if xy is None:
                # d is a multiple of n'; extremely unlikely (n'~2^180). Record None.
                r2 = dict(r); r2["X_Eprime"] = ""; r2["Y_Eprime"] = ""
            else:
                r2 = dict(r); r2["X_Eprime"] = hex(xy[0])[2:]; r2["Y_Eprime"] = hex(xy[1])[2:]
            w.writerow(r2)
            n_done += 1
            if n_done % 10000 == 0:
                el = time.time() - t0
                print(f"  {n_done}/100023  ({el:.1f}s, {n_done/el:.0f}/s)", flush=True)
el = time.time() - t0
print(f"derived {n_done} constructed [d]G' on E' in {el:.1f}s", flush=True)
print(f"wrote {out_c}", flush=True)
print("\nSTEP 2 COMPLETE. NO E3 computed yet (per prereg -- null freezes next).", flush=True)
