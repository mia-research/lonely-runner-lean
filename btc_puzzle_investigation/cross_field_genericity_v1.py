#!/usr/bin/env python3
"""
cross_field_genericity_v1.py

"Is secp256k1 special?" -- held p fixed in curve_alteration (swept b); here we sweep
the FIELD. Same Koblitz form y^2=x^3+7 (a=0) over several primes: secp192k1_p,
secp224k1_p, secp256k1_p, a generic random 256-bit prime, plus P-256 (a=-3, j!=0)
as an out-group. For each: generate known-d keys, measure generator-agnostic point
statistics and the leak MI(Xmod7 ; d mod 6). secp256k1 an outlier => a real anomaly;
matches the family => generic. Plant fires. Exact ints except ranked MI.
"""
import numpy as np
from angular_interference_scaling_v1 import conditional

def tonelli(a, p):
    a %= p
    if a == 0: return 0
    if pow(a, (p - 1) // 2, p) != 1: return None
    if p % 4 == 3: return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r

def ec_mul(k, a, p, base):
    """affine k*base on y^2=x^3+ax+b over F_p (b unused in the law)."""
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        if P == Q:
            lam = (3 * x1 * x1 + a) * pow(2 * y1, p - 2, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    R = None; Q = base
    while k:
        if k & 1: R = add(R, Q)
        Q = add(Q, Q); k >>= 1
    return R

def find_base(a, b, p):
    for x in range(1, 200000):
        rhs = (x * x * x + a * x + b) % p
        if rhs == 0: continue
        y = tonelli(rhs, p)
        if y is not None: return (x, y)
    return None

FIELDS = {
    "secp192k1": (0xfffffffffffffffffffffffffffffffffffffffeffffee37, 0, 7),
    "secp224k1": (0xfffffffffffffffffffffffffffffffffffffffffffffffeffffe56d, 0, 7),
    "secp256k1": (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F, 0, 7),
    "randprime": (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC0D, 0, 7),
    "P-256(j!=0)": (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
                    -3, 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b),
}

def main():
    NK = 350
    rng0 = np.random.default_rng(7)
    print(f"CROSS-FIELD GENERICITY  (y^2=x^3+ax+b, {NK} known-d keys/field)")
    print(f"{'field':>13} {'Xmod7 chi2(6)':>14} {'MI-z(Xmod7;d%6)':>16} {'X-top3 chi2(7)':>15}")
    for name, (p, a, b) in FIELDS.items():
        base = find_base(a, b, p)
        ds = [1 + int.from_bytes(rng0.bytes(32), "big") % (p - 2) for _ in range(NK)]
        Xs = []
        for d in ds:
            R = ec_mul(d, a, p, base)
            Xs.append(R[0] if R else 0)
        xm7 = np.array([x % 7 for x in Xs]); xt3 = np.array([x >> (x.bit_length() - 3) if x.bit_length() >= 3 else 0 for x in Xs])
        h7 = np.bincount(xm7, minlength=7); e7 = NK / 7          # noqa: float (report)
        c7 = float(((h7 - e7) ** 2 / e7).sum())                 # noqa: float (report)
        ht = np.bincount(xt3, minlength=8); et = NK / 8          # noqa: float
        ct = float(((ht - et) ** 2 / et).sum())                 # noqa: float
        d6 = np.array([d % 6 for d in ds])
        rng = np.random.default_rng(3)
        z = conditional(xm7, d6, [NK//2, NK], 200, rng)[-1][2]
        print(f"{name:>13} {c7:>14.1f} {z:>16.2f} {ct:>15.1f}")
    # PLANT
    ds = [1 + int(x) for x in np.random.default_rng(9).integers(0, 1 << 40, NK)]
    d6 = np.array([d % 6 for d in ds]); leak = d6.copy()
    z = conditional(leak, d6, [NK//2, NK], 200, np.random.default_rng(3))[-1][2]
    print(f"\n[PLANT] leak(d%6) vs d%6: z={z:.0f} (detector fires)")
    print("secp256k1 typical if its chi2/leak-z sit inside the family spread.")

if __name__ == "__main__":
    main()
