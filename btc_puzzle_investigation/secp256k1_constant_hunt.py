"""Pure-math discovery — is any secp256k1 constant unexpectedly structured?
Discipline: for each probe, compute secp256k1's value AND a control distribution
over random comparable constants; flag ONLY outliers (genuine feature) vs typical
(coincidence). Exact integers. No exploit angle — just 'is this number special'."""
import random
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
beta = pow(3, (p-1)//3, p)
lam  = pow(2, (n-1)//3, n)
t = p + 1 - n
import math
f = math.isqrt((4*p - t*t)//3)

def cf_maxpq(a, b):
    """largest partial quotient in the continued fraction of a/b."""
    m = 0
    while b:
        q = a // b; m = max(m, q); a, b = b, a - q*b
    return m
def smooth_part(m, bound=100000):
    s = 1
    for q in range(2, bound):
        while m % q == 0: s *= q; m //= q
        if q*q > m: break
    return s
def hamming(x): return bin(x).count("1")

rng = random.Random(2718)
def control(fn, mod, N=3000):
    return sorted(fn(rng.randrange(1, mod), mod) for _ in range(N))
def pct(val, dist):
    import bisect
    return 100.0 * bisect.bisect_left(dist, val) / len(dist)

print("=== PROBE 1: near-rational structure (max partial quotient of ratio/modulus) ===")
print("   large max-PQ ⇒ the ratio is anomalously close to a simple fraction")
ctrl_p = control(cf_maxpq, p); ctrl_n = control(cf_maxpq, n)
for name, a, mod, ctrl in [("Gx/p", Gx, p, ctrl_p), ("Gy/p", Gy, p, ctrl_p),
                           ("beta/p", beta, p, ctrl_p), ("lambda/n", lam, n, ctrl_n),
                           ("n/p", n, p, ctrl_p), ("t/f (=~sqrt3)", t, f, None)]:
    mpq = cf_maxpq(a, mod)
    if ctrl is not None:
        print(f"  {name:14s} maxPQ={mpq:<22} bits={mpq.bit_length():>3}  control-percentile={pct(mpq,ctrl):5.1f}%  "
              f"(ctrl median 2^{ctrl[len(ctrl)//2].bit_length()-1}, max 2^{ctrl[-1].bit_length()-1})")
    else:
        print(f"  {name:14s} maxPQ={mpq}  bits={mpq.bit_length()}")

print("\n=== PROBE 2: smooth part (largest product of small primes dividing the constant) ===")
ctrl_sp = sorted(smooth_part(rng.randrange(1, p)) for _ in range(3000))
for name, v in [("Gx", Gx), ("Gy", Gy), ("beta", beta), ("lambda", lam), ("t", t), ("f", f), ("n-1", n-1), ("p-1", p-1)]:
    sp = smooth_part(v)
    print(f"  {name:8s} smooth-part={sp:<12} (bits {sp.bit_length():>2})  percentile vs random={pct(sp,ctrl_sp):5.1f}%")

print("\n=== PROBE 3: Hamming weight of the constants (256-bit) ===")
ctrl_hw = sorted(hamming(rng.randrange(1, 1 << 256)) for _ in range(5000))
for name, v in [("p", p), ("n", n), ("Gx", Gx), ("Gy", Gy), ("beta", beta), ("lambda", lam)]:
    print(f"  {name:8s} HW={hamming(v):>3}/256   percentile vs random={pct(hamming(v),ctrl_hw):5.1f}%")

print("\n=== PROBE 4: simple cross-relations among constants (mod p and mod n) ===")
rels = {
    "Gy^2-Gx^3 mod p (=b)": (Gy*Gy - Gx*Gx*Gx) % p,
    "Gx*beta - lam*Gx? no": None,
    "Gx + Gy mod p": (Gx+Gy) % p,
    "Gx*Gy mod p": (Gx*Gy) % p,
    "beta*lam relation": None,
}
print(f"  Gy^2 - Gx^3 mod p = {(Gy*Gy-Gx*Gx*Gx)%p}  (must be b=7: {(Gy*Gy-Gx*Gx*Gx)%p==7})")
print(f"  beta^2+beta+1 mod p = {(beta*beta+beta+1)%p}  lam^2+lam+1 mod n = {(lam*lam+lam+1)%n}")
print(f"  is Gx a small multiple of Gy mod p? Gx*Gy^-1 mod p = {(Gx*pow(Gy,-1,p))%p} (small? no)")
print(f"  p - n = t - 1 ? {p-n == t-1}   (Hasse identity, trivially yes)")
