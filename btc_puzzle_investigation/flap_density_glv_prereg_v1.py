#!/usr/bin/env python3
"""
PREREG + EXECUTE: is the base flap density of P=dG biased for 130-bit scalars vs 256-bit? Exact ints.

HYPOTHESIS (user): GLV-cell rigidity for a 130-bit d pushes P=dG out of the 1/4 flap, into the 3/4 core.
OBJECT: rho_flap(S) = #{d in S: eps(dG)=FLAP} / |S|,  eps = exact Eisenstein/Dedekind flap classifier
        (ARM-0-validated: mu6-invariant, ~1/4 density).
ARMS (N points each): S130 = d uniform in [2^129,2^130);  S256 = d uniform in [1,N_ord);
                      SREF = uniform random VALID abscissas (the TRUE flap fraction p*, point-native).
NULL/CONTROL: all three densities equal p* if dG is generic. Test S130 vs S256 (two-proportion, exact).
DECISION: |z| = |k130/N - k256/N| / sqrt(2 p*(1-p*)/N).  FIRES iff |z| > 4 (crush bars, one primary cell).
POWER: N=1e5 -> SE(diff) ~ 0.0019 -> detects a real gap >= 0.008 at 4 sigma; the 6000-sample 'gap'
       (0.021) would show at ~11 sigma if real.
FALSIFY: gap -> 0 (both ~ p*)  => the 2.7-sigma at n=6000 was sampling noise; no density bias, no lever.
         gap persists |z|>4     => real bias (report magnitude+scope; note GLV-decomp mechanism is
                                   object-level questionable since P=dG is decomposition-independent).
No float in the signal path (eps is exact int). z-score is a reported statistic on integer counts.
"""
import sys, random
from avenue5_only import p, R1, R2, DET, eis_p
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
RHO = (BETA + 1) % p
N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def cent(m):
    m %= p
    return m - p if 2 * m > p else m


def extract_a():
    for X in range(1, 80):
        ar, br = eis_p(X); num = p * (ar * R2[1] - br * R2[0])
        if num % DET == 0:
            m = (num // DET) % p
            if m:
                return m * pow(X, p - 2, p) % p
A = extract_a()


def eps(X):
    s = A * X % p
    return 1 if 2 * abs(cent(s) - cent(RHO * s % p)) > p else 0


# ---- Jacobian EC with precomputed 2^i * G, batch inversion ----
def _dbl(P):
    X, Y, Z = P
    if Y == 0:
        return (0, 1, 0)
    A2 = X * X % p; B = Y * Y % p; C = B * B % p
    D = 2 * (((X + B) * (X + B) - A2 - C)) % p
    E = 3 * A2 % p; F = E * E % p
    X3 = (F - 2 * D) % p; Y3 = (E * (D - X3) - 8 * C) % p; Z3 = 2 * Y * Z % p
    return (X3, Y3, Z3)


def _add(P1, P2):
    X1, Y1, Z1 = P1; X2, Y2, Z2 = P2
    if Z1 == 0:
        return P2
    if Z2 == 0:
        return P1
    Z1Z1 = Z1 * Z1 % p; Z2Z2 = Z2 * Z2 % p
    U1 = X1 * Z2Z2 % p; U2 = X2 * Z1Z1 % p
    S1 = Y1 * Z2 * Z2Z2 % p; S2 = Y2 * Z1 * Z1Z1 % p
    if U1 == U2:
        return _dbl(P1) if S1 == S2 else (0, 1, 0)
    H = (U2 - U1) % p; r = (S2 - S1) % p
    HH = H * H % p; HHH = H * HH % p; V = U1 * HH % p
    X3 = (r * r - HHH - 2 * V) % p; Y3 = (r * (V - X3) - S1 * HHH) % p; Z3 = Z1 * Z2 * H % p
    return (X3, Y3, Z3)


TABLE = []
_Q = (GX, GY, 1)
for _ in range(256):
    zi = pow(_Q[2], p - 2, p); zi2 = zi * zi % p
    TABLE.append((_Q[0] * zi2 % p, _Q[1] * zi2 * zi % p))
    _Q = _dbl(_Q)


def mul_jac(k):
    R = (0, 1, 0); i = 0
    while k:
        if k & 1:
            tx, ty = TABLE[i]; R = _add(R, (tx, ty, 1))
        k >>= 1; i += 1
    return R


def flap_count_scalars(scalars):
    jac = [mul_jac(k) for k in scalars]
    Zs = [j[2] for j in jac]
    pref = [1] * (len(Zs) + 1)
    for i, z in enumerate(Zs):
        pref[i + 1] = pref[i] * z % p
    inv = pow(pref[-1], p - 2, p)
    cnt = 0
    for i in range(len(Zs) - 1, -1, -1):
        zi = inv * pref[i] % p; inv = inv * Zs[i] % p
        X = jac[i][0] * zi * zi % p
        cnt += eps(X)
    return cnt


def flap_count_absc(rng, N):
    cnt = tot = 0
    while tot < N:
        X = rng.randrange(1, p)
        if pow((X * X % p * X + 7) % p, (p - 1) // 2, p) == 1:
            cnt += eps(X); tot += 1
    return cnt


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    rng = random.Random(20260721)
    lo130 = 1 << 129
    s130 = [lo130 + rng.randrange(lo130) for _ in range(N)]
    s256 = [1 + rng.randrange(N_ORD - 1) for _ in range(N)]
    print(f"# flap density: 130-bit dG vs 256-bit dG vs true fraction | N={N} | a bits={A.bit_length()}", flush=True)
    k130 = flap_count_scalars(s130); print(f"#   S130 done: {k130}/{N}", flush=True)
    k256 = flap_count_scalars(s256); print(f"#   S256 done: {k256}/{N}", flush=True)
    kref = flap_count_absc(rng, N);  print(f"#   SREF done: {kref}/{N}", flush=True)
    # exact rational densities; z on integer counts (report-only float)
    def dens(k): return k / N
    pstar = kref / N
    var = 2 * pstar * (1 - pstar) / N
    z = (k130 - k256) / N / (var ** 0.5) if var > 0 else 0.0
    print(f"\n=== RESULT (N={N}) ===")
    print(f"  S130 (130-bit dG): {k130}/{N} = {dens(k130):.5f}")
    print(f"  S256 (256-bit dG): {k256}/{N} = {dens(k256):.5f}")
    print(f"  SREF (true frac ): {kref}/{N} = {pstar:.5f}")
    print(f"  gap(130-256) = {dens(k130)-dens(k256):+.5f}   z = {z:+.2f}   -> "
          f"{'FIRES (density bias)' if abs(z) > 4 else 'null (no bias; 6000-sample gap was noise)'}")
    print(f"  |S130-ref| z = {(k130-kref)/N/(var**0.5):+.2f}   |S256-ref| z = {(k256-kref)/N/(var**0.5):+.2f}")


if __name__ == "__main__":
    main()
