#!/usr/bin/env python3
"""
struct_probes.py  —  Plan v4 Tests B, C, F (exact-integer, secp256k1).

  B  sum-product energy of curve-point coordinate sets vs random / AP controls
  C  isogeny / twist probe: curve-order primality (no Pohlig-Hellman on E) +
     twist-order smoothness
  F  GLV / CM endomorphism: verify (beta,lambda), GLV-decompose solved keys,
     test (d1,d2) distribution vs random

Verdicts from integer counts; any float is a reported ratio only. Curve ops
imported from puzzle_kangaroo.py.

Usage: python3 struct_probes.py [B|C|F|all]
"""
import sys, csv, secrets
from collections import Counter
from puzzle_kangaroo import add, G, N_ORD, P, Gx, Gy

def mul(k, Pt):
    R = None; A = Pt; k %= N_ORD
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R

def load_solved(maxrows=200):
    """Return (d, x) for solved puzzles with a known private key (hex 0x...)."""
    out = []
    with open("solved_puzzles_xy.csv") as f:
        for row in csv.DictReader(f):
            pk = row["private_key"].strip()
            if pk:
                d = int(pk, 16) if pk.lower().startswith("0x") else int(pk)
                x = int(row["X"], 16)
                if d > 0:
                    out.append((d, x))
            if len(out) >= maxrows:
                break
    return out

# ---------- Test B : sum-product energy ----------
def additive_energy(vals, mod):
    c = Counter()
    for a in vals:
        for b in vals:
            c[(a + b) % mod] += 1
    return sum(v * v for v in c.values())     # #{a+b=c+d}, exact integer

def multiplicative_energy(vals, mod):
    c = Counter()
    for a in vals:
        for b in vals:
            c[(a * b) % mod] += 1
    return sum(v * v for v in c.values())     # #{ab=cd}, exact integer

def load_100k_XY(n, bits_min=40):
    """First n (X,Y) from the 100k synthetic set (bits>=bits_min)."""
    xs = []; ys = []
    with open("constructed_keys_1to160_100k_exact.csv") as f:
        for row in csv.DictReader(f):
            if int(row["bits"]) >= bits_min:
                xs.append(int(row["X"], 16)); ys.append(int(row["Y"], 16))
            if len(xs) >= n:
                break
    return xs, ys

def test_B(m=2000, Bnull=40):
    print(f"# TEST B  sum-product energy   set size m={m}, null draws={Bnull}")
    print(f"# curve-structure test: uses {m} real curve points from the 100k set, not")
    print("# the 82 solved keys. baseline (random F_p subset): E ~ m^2 for BOTH energies.")
    print("# structure => one energy >> m^2.  AP control should blow up additive energy.\n")
    real_x, real_y = load_100k_XY(m)
    m = len(real_x)
    orbit = []; Pt = None                                           # X(jG), consecutive (incremental)
    for _ in range(m):
        Pt = add(Pt, G); orbit.append(Pt[0])
    ap = [(12345 + j * 999983) % P for j in range(m)]              # arithmetic progression
    sets = {"100k pubkey_X": real_x, "100k pubkey_Y": real_y,
            "orbit jG X": orbit, "AP control": ap}
    # matched null: random F_p subsets
    nulls_add = []; nulls_mul = []
    for _ in range(Bnull):
        s = [secrets.randbelow(P) for _ in range(m)]
        nulls_add.append(additive_energy(s, P)); nulls_mul.append(multiplicative_energy(s, P))
    def rank(val, nulls):        # fraction of null >= val (exact integer rank)
        ge = sum(1 for x in nulls if x >= val)
        return ge, len(nulls)
    base = m * m
    print(f"  {'set':<18}{'E_add':>14}{'E_add/m^2':>11}{'E_mul':>14}{'E_mul/m^2':>11}  rank(add,mul)")
    for name, s in sets.items():
        ea = additive_energy(s, P); em = multiplicative_energy(s, P)
        ga, na = rank(ea, nulls_add); gm, nm = rank(em, nulls_mul)
        print(f"  {name:<18}{ea:>14}{ea/base:>11.3f}{em:>14}{em/base:>11.3f}"
              f"   {ga}/{na}, {gm}/{nm}")
    print("\n  read: solved/orbit/random E ~ m^2 and rank mid-null => sum-product-random")
    print("        (no exploitable additive+multiplicative structure). AP add-energy huge = sanity.")

# ---------- Test C : isogeny / twist ----------
def small_factors(m, bound=1 << 20):
    fs = []; d = 2
    while d < bound and d * d <= m:
        while m % d == 0:
            fs.append(d); m //= d
        d += 1 if d == 2 else 2
    return fs, m      # (small prime factors found, remaining cofactor)

def is_probable_prime(n, rounds=40):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for _ in range(rounds):
        a = 2 + secrets.randbelow(n - 3)
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def test_C():
    print("# TEST C  isogeny / twist probe\n")
    ok_order = mul(N_ORD, G) is None
    print(f"  n*G == O (G has order n): {ok_order}")
    print(f"  curve order n prime:     {is_probable_prime(N_ORD)}  (cofactor 1)")
    print("    => E(F_p) is cyclic of prime order: NO nontrivial subgroup, NO small-order")
    print("       point, NO Pohlig-Hellman / isogeny-descent residue on E. d has no")
    print("       recoverable 'd mod l' for small l (l | n impossible, n prime).")
    twist = 2 * P + 2 - N_ORD                       # #E' = p+1+t, with #E = p+1-t = n
    fs, cof = small_factors(twist, bound=1 << 24)   # trial-divide to 2^24
    print(f"\n  twist order n' = 2p+2-n  ({twist.bit_length()} bits):")
    print(f"    prime factors < 2^24: {sorted(set(fs)) if fs else 'none'}")
    print(f"    remaining cofactor: {cof.bit_length()} bits,  probable-prime: {is_probable_prime(cof)}")
    smooth = cof == 1 or (cof.bit_length() < 40)
    print(f"    => twist is {'SMOOTH (would enable a twist attack IF off-curve pts accepted)' if smooth else 'NOT smooth (large factor remains)'}")
    print("    (moot regardless: a published on-curve pubkey never touches the twist.)")

# ---------- Test F : GLV / CM ----------
BETA   = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
LAMBDA = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

def ndiv(a, b):                     # nearest integer to a/b, b>0, exact
    q, r = divmod(a, b)
    if 2 * r >= b: q += 1
    return q

def gauss_reduce(v1, v2):
    dot = lambda a, b: a[0] * b[0] + a[1] * b[1]
    while True:
        if dot(v2, v2) < dot(v1, v1):
            v1, v2 = v2, v1
        mu = ndiv(dot(v1, v2), dot(v1, v1))
        if mu == 0:
            return v1, v2
        v2 = (v2[0] - mu * v1[0], v2[1] - mu * v1[1])

def glv_decompose(d):
    """d1 + d2*lambda ≡ d (mod n), with |d1|,|d2| small. Exact integer Babai."""
    v1, v2 = gauss_reduce((N_ORD, 0), (-LAMBDA % N_ORD, 1))
    det = v1[0] * v2[1] - v1[1] * v2[0]
    tx, ty = d, 0
    c1n = tx * v2[1] - ty * v2[0]
    c2n = v1[0] * ty - v1[1] * tx
    if det < 0:
        det, c1n, c2n = -det, -c1n, -c2n
    c1 = ndiv(c1n, det); c2 = ndiv(c2n, det)
    close = (c1 * v1[0] + c2 * v2[0], c1 * v1[1] + c2 * v2[1])
    return d - close[0], -close[1]     # (d1, d2)

def test_F():
    print("# TEST F  GLV / CM endomorphism\n")
    print(f"  beta^3 == 1 (mod p): {pow(BETA,3,P) == 1}    lambda^3 == 1 (mod n): {pow(LAMBDA,3,N_ORD) == 1}")
    # endomorphism check: (beta*x, y) == lambda*(x,y)
    ok = True
    for _ in range(5):
        Pt = mul(1 + secrets.randbelow(N_ORD - 1), G)
        if ((BETA * Pt[0]) % P, Pt[1]) != mul(LAMBDA, Pt):
            ok = False
    print(f"  endomorphism (beta*x,y) == lambda*P on random points: {ok}")
    solved = load_solved()
    print(f"\n  GLV-decompose {len(solved)} solved keys; checking d1+d2*lambda == d (mod n):")
    bad = 0; halfbits = []
    for d, _ in solved:
        d1, d2 = glv_decompose(d)
        if (d1 + d2 * LAMBDA - d) % N_ORD != 0:
            bad += 1
        halfbits.append((max(abs(d1), abs(d2))).bit_length())
    print(f"    decompositions valid: {len(solved) - bad}/{len(solved)}")
    print(f"    max(|d1|,|d2|) bit-length: min={min(halfbits)} max={max(halfbits)} "
          f"(≈ n/2 ~ 128 confirms balanced GLV; kangaroo gain ~sqrt(2), the known constant)")
    # distribution probe: parity of d1 for real keys vs random keys of same bits
    real_par = Counter(); rnd_par = Counter()
    for d, _ in solved:
        d1, _ = glv_decompose(d); real_par[d1 & 1] += 1
        nb = d.bit_length(); rd = (1 << (nb - 1)) + secrets.randbelow(1 << (nb - 1)) if nb > 1 else d
        rd1, _ = glv_decompose(rd); rnd_par[rd1 & 1] += 1
    print(f"    d1 parity  real: {dict(real_par)}   random-same-bits: {dict(rnd_par)}")
    print("    (only ~80 keys: a probe, not a powered test; gross bias would still show.)")

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("B", "all"): test_B()
    if which in ("C", "all"): print(); test_C()
    if which in ("F", "all"): print(); test_F()

if __name__ == "__main__":
    main()
