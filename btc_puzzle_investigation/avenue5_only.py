#!/usr/bin/env python3
"""
Only Avenue #5: affine relation V = M*U + c.
Uses d and X from the npz (if available) or generates random keys.
"""
import sys, math, random
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

def main():
    print("="*70)
    print("Avenue #5: Affine relation V = M*U + c")
    print("="*70)

    # Try to load from npz
    d_vals = None; x_vals = None
    try:
        data = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
        keys = list(data.keys())
        print("Available keys:", keys)
        if 'd' in keys and 'X' in keys:
            d_vals = data['d']
            x_vals = data['X']
            print(f"Loaded {len(d_vals)} synthetic keys from npz.")
        else:
            print("Keys 'd' and 'X' not found. Will generate random keys.")
    except Exception as e:
        print(f"Could not load npz: {e}. Generating random keys.")

    if d_vals is None:
        print("Generating 200 random keys using Python random...")
        rng2 = random.Random(42)
        d_vals = [rng2.randrange(1, n) for _ in range(200)]
        print("Computing x-coordinates (scalar multiplication)...")
        x_vals = [scalar_mul(int(d))[0] for d in d_vals]

    # Convert to numpy arrays of floats (exact conversion)
    # d_vals and x_vals may be Python ints; ensure they are ints.
    # Then compute U and V as lists of tuples, then convert to float arrays.
    U_list = [eis_p(int(x)) for x in x_vals]
    V_list = [eis_n(int(d)) for d in d_vals]

    # Convert to numpy float arrays (2D)
    U = np.array(U_list, dtype=float)
    V = np.array(V_list, dtype=float)

    # Fit linear model V = U * M + c
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
