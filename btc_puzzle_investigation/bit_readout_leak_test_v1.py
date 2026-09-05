#!/usr/bin/env python3
# ============================================================================================
# PRE-REGISTRATION (committed before the run)
# IDEA UNDER TEST (external review Rec #3 / master frontier X.1 & VIII.3): cheap, DLP-free,
#   NON-mu6-covariant coordinate-bit readouts of the public point [d]G leak the scalar d.
#   These live in the V-3 unbounded-degree GAP (a bit is high-degree), the master's OWN
#   untested complement to the mu6-isotype-pure readouts. GLV-flatness (VIII.2) does NOT apply.
#
# OBJECT: E: y^2 = x^3 + 7 over F_p with n = #E(F_p) PRIME (prime-order, like secp; j=0 CM).
#   Bijection d <-> P_d=[d]G, d in 1..n-1 (P_0=O excluded). All curve arithmetic exact (Python int).
#
# READOUTS F: Z/n -> small set  (each a cheap function of the PUBLIC coordinates, no d needed):
#   x&1 (LSB x), y&1 (LSB y), hi(x)=[2x>=p] (MSB x), hi(y)=[2y>=p], x%4, x&15 (low nibble),
#   (x&1,y&1) joint.  These are non-covariant under mu6 (beta-mult avalanches the bits).
#
# STATISTIC (single-frequency concentration; "does the bit correlate with a character e_n(a d)?"):
#   For F as a length-n vector indexed by d: Chat(a) = (1/n) sum_d F(d) e_n(-a d)  (numpy FFT).
#   C(F) = max_{a != 0} |Chat(a)| / rms0(F),  rms0 = sqrt(mean((F-mean F)^2)).  A perfectly aligned
#   F (F=e_n(a0 d)) gives C ~ 1; a random function of d gives C ~ sqrt(log n / n) (the floor).
#   ** float appears ONLY in this FFT statistic, which is ranked against a matched permutation null;
#      the signal-path arithmetic (curve, coords, bits) is all exact int. (integrity rule: allowed.) **
#
# NULL (matched): permute the VALUES of F across d (random bijection of the d-index) -> preserves the
#   exact value multiset, destroys any d-alignment. B=300 reps. z=(C_real-mean)/std; rank-p =
#   (#null >= real + 1)/(B+1).  This is the ONLY correct null: it asks "is there EXCESS d-concentration
#   beyond a random function with the SAME value distribution?" (shuffle-of-values, not np.roll).
#
# CONTROLS (must fire as stated or the run is VOID):
#   PLANT (positive): F(d) = [ (a0*d mod n) < n/2 ], a0=7919 -> an aligned square wave at freq a0.
#     MUST give z >> 5 (statistic detects a real single-frequency leak).
#   RAND  (negative): F(d) = random bit -> MUST give |z| < 4 (no false positive).
#   Also report the PLANT detection floor by mixing fraction m (m in {1,.3,.1,.03}) to calibrate power.
#
# FALSIFICATION / readings (decidable both ways, no verdict of closure):
#   - A real readout with z above the plant-calibrated detection floor AND rank-p small => a coordinate
#     bit concentrates at a single frequency at this scale: a POSITIVE to drill (which bit, which a, mu3
#     grading, does it persist to larger n / other p).
#   - All real readouts at the matched floor => SCOPED null: "no single-frequency concentration above
#     floor phi for these coordinate-bit readouts at this p; distributed/multi-freq structure, larger n,
#     and 2^256 are UNTESTED" (per the language rule -- a bounded magnitude, not "no structure").
# ============================================================================================
import numpy as np

# ---- exact curve arithmetic over F_p, E: y^2 = x^3 + 7 ----
def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def ecount(p):  # #E(F_p) = p + 1 + sum_x legendre(x^3+7)
    s = 0
    for x in range(p):
        s += legendre((x * x % p * x + 7) % p, p)
    return p + 1 + s

def find_prime_order_curve(p_lo, p_hi, n_min):
    from sympy import isprime, nextprime
    p = nextprime(p_lo - 1)
    while p < p_hi:
        if p % 6 == 1:                        # p = 1 mod 6 : j=0 CM / GLV present, matches secp
            n = ecount(p)
            if n >= n_min and isprime(n):
                return p, n
        p = nextprime(p)
    return None, None

def sqrt_mod(a, p):
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
        t2, i = t, 0
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r

def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        lam = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)

def first_point(p):
    for x in range(p):
        v = (x * x % p * x + 7) % p
        y = sqrt_mod(v, p)
        if y is not None:
            return (x, y)
    return None

# ---- the statistic + matched null ----
def concentration(F):
    F = F.astype(np.float64)
    F0 = F - F.mean()
    rms = np.sqrt((F0 * F0).mean())
    if rms == 0: return 0.0
    spec = np.abs(np.fft.fft(F0)) / len(F)
    return spec[1:].max() / rms          # max over a != 0

def test_readout(F, B, rng):
    c_real = concentration(F)
    null = np.empty(B)
    for b in range(B):
        null[b] = concentration(rng.permutation(F))
    z = (c_real - null.mean()) / (null.std() + 1e-15)
    rankp = (np.sum(null >= c_real) + 1) / (B + 1)
    return c_real, z, rankp

def main():
    rng = np.random.default_rng(20260719)
    print("Finding prime-order E: y^2=x^3+7 ...")
    p, n = find_prime_order_curve(50000, 200000, 40000)
    print(f"  p={p}  n=#E={n}  (n prime, p=1 mod6)")
    # enumerate P_d = [d]G, d=1..n-1
    G = first_point(p); print(f"  G={G}")
    xd = np.empty(n, dtype=np.int64); yd = np.empty(n, dtype=np.int64)
    P = None
    for d in range(1, n):
        P = ec_add(P, G, p); xd[d], yd[d] = P
    # sanity: [n]G should be O  (P after d=n-1 plus G)
    assert ec_add(P, G, p) is None, "order check failed"
    print("  order check [n]G=O: OK")
    x = xd.copy(); y = yd.copy()               # index d; d=0 slot is 0 (O excluded from stats below)

    readouts = {
        "x & 1        ": (x & 1),
        "y & 1        ": (y & 1),
        "hi(x)=[2x>=p]": ((2 * x >= p).astype(np.int64)),
        "hi(y)=[2y>=p]": ((2 * y >= p).astype(np.int64)),
        "x mod 4      ": (x % 4),
        "x & 15       ": (x & 15),
        "(x&1,y&1)    ": ((x & 1) * 2 + (y & 1)),
    }
    B = 300
    print(f"\nMATCHED-NULL CONCENTRATION TEST  (B={B} value-permutations; escape = z>=5 AND rank-p<0.01)")
    print(f"{'readout':<14} {'C(F)':>9} {'z':>8} {'rank-p':>9}")
    print("-" * 44)
    # controls first
    a0 = 7919
    d_idx = np.arange(n)
    plant = ((a0 * d_idx) % n < n // 2).astype(np.int64); plant[0] = 0
    c, z, rp = test_readout(plant, B, rng); print(f"{'PLANT(a0)':<14} {c:9.5f} {z:8.2f} {rp:9.4f}   <- positive control MUST fire")
    randf = rng.integers(0, 2, n)
    c, z, rp = test_readout(randf, B, rng); print(f"{'RANDOM':<14} {c:9.5f} {z:8.2f} {rp:9.4f}   <- negative control MUST be null")
    print("-" * 44)
    results = {}
    for name, F in readouts.items():
        c, z, rp = test_readout(F.astype(np.int64), B, rng)
        results[name] = (c, z, rp)
        flag = "  ** ESCAPE **" if (z >= 5 and rp < 0.01) else ""
        print(f"{name:<14} {c:9.5f} {z:8.2f} {rp:9.4f}{flag}")

    # power calibration: mix fraction m of the aligned plant into a random base; smallest m that fires
    print("\nPOWER (detection floor): mix m*plant + (1-m)*noise, z of the mix:")
    base = rng.standard_normal(n)
    for m in (1.0, 0.3, 0.1, 0.03, 0.01):
        sig = ((a0 * d_idx) % n < n // 2).astype(np.float64)
        mix = m * sig + (1 - m) * (base - base.min()) / (base.max() - base.min())
        c, z, rp = test_readout(mix, 120, rng)
        print(f"  m={m:<5} z={z:8.2f} rank-p={rp:.4f}")
    print("\n[done] Signal path exact int; FFT statistic ranked vs matched value-permutation null.")

if __name__ == "__main__":
    main()
