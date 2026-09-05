#!/usr/bin/env python3
"""
Combined Avenue #1 (#epsilon conditional) and #5 (affine relation).
Self-contained; uses numpy only. No sklearn.
"""
import sys, math, csv, random
from collections import Counter
import numpy as np

# ----- Constants -----
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171

# ----- Gauss reduction -----
def rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de)
    return q + 1 if 2*r >= de else q

def gauss_reduce(u, v):
    dot = lambda a, b: a[0]*b[0] + a[1]*b[1]
    while True:
        if dot(v,v) < dot(u,u):
            u, v = v, u
        m = rdiv(dot(u,v), dot(u,u))
        v = (v[0] - m*u[0], v[1] - m*u[1])
        if dot(v,v) >= dot(u,u):
            return u, v

def reduced_basis_from_pi(pi):
    a, b = pi
    return gauss_reduce((a, b), (-b, a - b))

pi_p = (aP, bP)
R1, R2 = reduced_basis_from_pi(pi_p)
DET = R1[0]*R2[1] - R1[1]*R2[0]

pi_n = (aP - 1, bP)
R1n, R2n = reduced_basis_from_pi(pi_n)
DETn = R1n[0]*R2n[1] - R1n[1]*R2n[0]

def eis_generic(X, R1b, R2b, DETb, prime):
    X = int(X) % prime
    c1 = rdiv(X * R2b[1], DETb)
    c2 = rdiv(-X * R1b[1], DETb)
    return (X - (c1*R1b[0] + c2*R2b[0]), -(c1*R1b[1] + c2*R2b[1]))

def eis_p(X):   return eis_generic(X, R1, R2, DET, p)
def eis_n(X):   return eis_generic(X, R1n, R2n, DETn, n)

def sextant(u, v):
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0:
            return k
        u, v = v, v - u
    return 0 if v >= 0 else 3

def gauss_round(z, R1b, R2b, DETb):
    x, y = z
    c1 = rdiv(x * R2b[1] - y * R2b[0], DETb)
    c2 = rdiv(-x * R1b[1] + y * R1b[0], DETb)
    return (x - (c1*R1b[0] + c2*R2b[0]), y - (c1*R1b[1] + c2*R2b[1]))

def get_epsilon(z):
    u, v = z
    z_rot = (-u - v, u)
    z_red = gauss_round(z_rot, R1, R2, DET)
    diff = (z_rot[0] - z_red[0], z_rot[1] - z_red[1])
    if diff == (0, 0):
        return 0
    # check if diff is parallel to R1 or R2
    cross1 = diff[0]*R1[1] - diff[1]*R1[0]
    cross2 = diff[0]*R2[1] - diff[1]*R2[0]
    if cross1 == 0:
        dot1 = diff[0]*R1[0] + diff[1]*R1[1]
        return 1 if dot1 > 0 else -1
    if cross2 == 0:
        dot2 = diff[0]*R2[0] + diff[1]*R2[1]
        return 1 if dot2 > 0 else -1
    # fallback (should not happen)
    return 0

# ----- Scalar multiplication -----
def scalar_mul(k):
    Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
    P = p
    def _dbl(Xx, Yy, Zz):
        if Yy == 0: return (0,1,0)
        A = (Xx*Xx) % P; B = (Yy*Yy) % P; C = (B*B) % P
        D = (2*(((Xx+B)*(Xx+B) - A - C))) % P
        E = (3*A) % P; F = (E*E) % P
        X3 = (F - 2*D) % P; Y3 = (E*(D - X3) - 8*C) % P
        Z3 = (2*Yy*Zz) % P; return (X3,Y3,Z3)
    def _add(P1, P2):
        X1,Y1,Z1 = P1; X2,Y2,Z2 = P2
        if Z1 == 0: return P2
        if Z2 == 0: return P1
        Z1Z1 = (Z1*Z1) % P; Z2Z2 = (Z2*Z2) % P
        U1 = (X1*Z2Z2) % P; U2 = (X2*Z1Z1) % P
        S1 = (Y1*Z2*Z2Z2) % P; S2 = (Y2*Z1*Z1Z1) % P
        if U1 == U2:
            if S1 != S2: return (0,1,0)
            return _dbl(X1,Y1,Z1)
        H = (U2 - U1) % P; r = (S2 - S1) % P
        HH = (H*H) % P; HHH = (H*HH) % P; V = (U1*HH) % P
        X3 = (r*r - HHH - 2*V) % P; Y3 = (r*(V - X3) - S1*HHH) % P
        Z3 = (Z1*Z2*H) % P; return (X3,Y3,Z3)
    R = (0,1,0); Q = (Gx, Gy, 1)
    while k > 0:
        if k & 1: R = _add(R, Q)
        Q = _dbl(Q[0], Q[1], Q[2]); k >>= 1
    Xx,Yy,Zz = R
    if Zz == 0: return None
    zi = pow(Zz, P-2, P); zi2 = (zi*zi) % P
    return ((Xx*zi2) % P, (Yy*zi2*zi) % P)

# ----- Build histogram (Avenue 1) -----
def build_histogram(points, nbins=20):
    hist = np.zeros((6, nbins, 3), dtype=int)
    diff_counter = Counter()
    for z in points:
        s = (z[0]*z[0] - z[0]*z[1] + z[1]*z[1]) / p
        if s < 0 or s > 0.75: continue
        k = sextant(z[0], z[1])
        idx = int(s // (0.75 / nbins))
        if idx >= nbins: idx = nbins - 1
        eps = get_epsilon(z)
        hist[k, idx, eps+1] += 1
        # collect diff
        u,v = z; z_rot = (-u-v, u); z_red = gauss_round(z_rot, R1, R2, DET)
        diff_counter[(z_rot[0]-z_red[0], z_rot[1]-z_red[1])] += 1
    return hist, diff_counter

def print_hist(hist):
    nbins = hist.shape[1]
    for k in range(6):
        for idx in range(nbins):
            row = hist[k, idx]
            if row.sum() == 0: continue
            s_low = idx * (0.75 / nbins); s_high = (idx+1) * (0.75 / nbins)
            core_frac = row[1] / row.sum() if row.sum()>0 else 0
            print(f"  {k} | {s_low:5.3f}-{s_high:5.3f} | {row[0]:4d} {row[1]:4d} {row[2]:4d} | {core_frac:.3f}")

# ----- Main -----
def main():
    print("="*70)
    print("Avenue #1: eps conditional distribution")
    print("="*70)
    rng = random.Random(12345)
    M = 50000
    zs = [eis_p(rng.randrange(1, p)) for _ in range(M)]
    hist, diff_counts = build_histogram(zs)
    print("\nHistogram by sextant and norm bin (columns: -R, 0, +R):")
    print_hist(hist)

    print("\nCorrection vector distribution (should be {0, ±R1, ±R2}):")
    for d, cnt in diff_counts.most_common(6):
        print(f"  {d}: {cnt} ({cnt/M*100:.2f}%)")

    eps_counts = Counter(get_epsilon(z) for z in zs)
    total = sum(eps_counts.values())
    print(f"\nMarginal eps: {dict(eps_counts)}")
    print(f"  -1: {eps_counts.get(-1,0)/total:.4f} (expected 0.125)")
    print(f"   0: {eps_counts.get(0,0)/total:.4f} (expected 0.75)")
    print(f"  +1: {eps_counts.get(1,0)/total:.4f} (expected 0.125)")

    # Real keys
    csv_path = "puzzles_verified.csv"
    try:
        rows = list(csv.DictReader(open(csv_path)))
        print(f"\nLoaded {len(rows)} real keys.")
        z_real = []
        for r in rows:
            d = int(r["private_key"], 16)
            x, y = scalar_mul(d)
            z_real.append(eis_p(x))
        hist_r, _ = build_histogram(z_real)
        print("\nReal keys histogram:")
        print_hist(hist_r)
        eps_r = Counter(get_epsilon(z) for z in z_real)
        total_r = sum(eps_r.values())
        print(f"\nReal eps: {dict(eps_r)} (expected 1/8,3/4,1/8)")
    except FileNotFoundError:
        print(f"\nFile {csv_path} not found. Skipping real keys.")

    # ----- Avenue 5: affine relation -----
    print("\n" + "="*70)
    print("Avenue #5: Affine relation V = M*U + c")
    print("="*70)

    try:
        data = np.load("constructed_keys_fullrange_v1.npz")
        d_vals = data['d']; x_vals = data['x']
        print(f"Loaded {len(d_vals)} synthetic keys.")
    except FileNotFoundError:
        print("constructed_keys_fullrange_v1.npz not found. Generating 200 random keys.")
        rng2 = np.random.default_rng(42)
        d_vals = rng2.integers(1, n, size=200)
        x_vals = np.array([scalar_mul(int(d))[0] for d in d_vals])

    U = np.array([eis_p(int(x)) for x in x_vals])
    V = np.array([eis_n(int(d)) for d in d_vals])

    # Fit V = U * M + c  (M is 2x2, c is 2)
    # We can solve using least squares: for each output coordinate separately.
    # Build design matrix [U, 1]
    Xd = np.hstack([U, np.ones((len(U),1))])
    coef_u, res_u, _, _ = np.linalg.lstsq(Xd, V[:,0], rcond=None)
    coef_v, res_v, _, _ = np.linalg.lstsq(Xd, V[:,1], rcond=None)
    M_est = np.array([coef_u[:2], coef_v[:2]])
    c_est = np.array([coef_u[2], coef_v[2]])
    print(f"Estimated M:\n{M_est}")
    print(f"Estimated c: {c_est}")

    V_pred = np.dot(U, M_est.T) + c_est
    residuals = V - V_pred
    mse = np.mean(residuals**2)
    print(f"MSE (coordinate units): {mse:.6f}")
    print(f"Std of residuals: {np.std(residuals, axis=0)}")

    diff_uv = V - U
    print(f"Mean(V - U): {np.mean(diff_uv, axis=0)}")
    print(f"Std(V - U): {np.std(diff_uv, axis=0)}")
    print("Basis slippage: R1_p - R1_n =", (R1[0]-R1n[0], R1[1]-R1n[1]))
    print("               R2_p - R2_n =", (R2[0]-R2n[0], R2[1]-R2n[1]))

if __name__ == "__main__":
    main()
