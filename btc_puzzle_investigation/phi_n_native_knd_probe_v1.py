#!/usr/bin/env python3
"""
phi(n)-NATIVE probe of the (n,k,D) decomposition on the 82 solved keys.

Motivation: prior work nulled "k has no structure" by testing k as an INTEGER
MAGNITUDE (raw bits). The phi(n)-residue framework says k should be read as a
UNIT in (Z/n)^x, and the surviving mode of the averaging operator P_n has
Ramanujan weight c_n(k). For coprime (n,k) that weight is mu(n): so the
framework predicts real keys should carry structure in
  - mu(n) / squarefreeness of n   (operator kills mu(n)=0 moduli)
  - omega(n) = # distinct prime factors   (low phi(n)/n = many factors)
  - the multiplicative order of k in (Z/n)^x, and k = +-1 mod n
        ( +-1 = the exact surviving Fourier mode of P_n ).

EXACT ONLY. No float in the signal path. (n,k) recomputed from d by minimizing
|n*(d-A) - k*A| over n<=256 (best rational approx of u=(d-A)/A). Null = matched
uniform-d draws in the SAME bit-band, same exact decomposition. Aggregation is a
uniform-rank test across keys (integer counts).
"""
import csv, random
from math import gcd
from fractions import Fraction

random.seed(20260710)
NMAX = 256
NULL_DRAWS = 4000          # matched uniform-d null per key
MIN_BITS = 20              # below this, u has too few states to be meaningful

# ---------- exact number theory ----------
def factorize(m):
    f = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def omega(m):
    return 0 if m <= 1 else len(factorize(m))

def mobius(m):
    if m == 1: return 1
    f = factorize(m)
    if any(e > 1 for e in f.values()): return 0
    return -1 if (len(f) % 2) else 1

def euler_phi(m):
    if m <= 1: return 1
    r = m
    for p in factorize(m):
        r -= r // p
    return r

def mult_order(a, n):
    """order of a in (Z/n)^x, or None if not coprime / n<=1."""
    a %= n
    if n <= 1 or gcd(a, n) != 1: return None
    o, x = 1, a % n
    while x != 1:
        x = (x * a) % n
        o += 1
        if o > n: return None
    return o

def best_nk(d, N):
    """best rational approx k/n of u=(d-A)/A, n<=NMAX, exact. returns (n,k)."""
    A = 1 << (N - 1)
    num = d - A            # 0 <= num < A, so u in [0,1)
    best = None            # (|n*num - k*A|, n, k)  minimise; tie -> smaller n
    for n in range(1, NMAX + 1):
        # k = round(n*num / A) exactly, via integer division on 2*n*num vs A
        k = (2 * n * num + A) // (2 * A)
        if k < 0: k = 0
        if k > n: k = n
        for kk in (k - 1, k, k + 1):
            if kk < 0 or kk > n: continue
            err = abs(n * num - kk * A)
            key = (err, n, kk)
            if best is None or key < best:
                best = key
    _, n, k = best
    g = gcd(k, n) if n else 1
    if g > 1:
        n //= g; k //= g
    return n, k

def features(d, N):
    n, k = best_nk(d, N)
    om = omega(n)
    mu = mobius(n)
    sqfree = 1 if mu != 0 else 0
    phi = euler_phi(n)
    phi_ratio = Fraction(phi, n) if n else Fraction(1)
    ordk = mult_order(k, n)               # None if n<=2 or non-coprime
    pm1 = 1 if (n > 2 and (k % n) in (1, n - 1)) else 0
    small_ord = None if ordk is None else (1 if ordk <= 2 else 0)
    return dict(n=n, k=k, omega=om, sqfree=sqfree, phi_ratio=phi_ratio,
                pm1=pm1, ordk=ordk, small_ord=small_ord)

# ---------- load solved keys ----------
rows = []
with open("puzzles_verified.csv") as fh:
    for r in csv.DictReader(fh):
        N = int(r["bits"]); d = int(r["private_key"], 16)   # pk column is hex
        if N >= MIN_BITS and r.get("onchain_pubkey_matches_our_X", "Y") != "N":
            rows.append((N, d))
print(f"solved keys used (N>={MIN_BITS}): {len(rows)}")

# ---------- per-key rank within matched null ----------
# For each numeric feature, count fraction of null draws with feature < real
# (and == real, to build a mid-rank). Aggregate the mid-ranks: under the null
# they are ~Uniform(0,1); we test mean-shift with an EXACT sign/rank statistic.
feat_num = ["omega", "sqfree", "phi_ratio", "pm1"]
ranks = {f: [] for f in feat_num}
ord_small_real = []   # for coprime-n keys: is ord(k) small?
n_list_real = []

for (N, d) in rows:
    rf = features(d, N)
    n_list_real.append(rf["n"])
    A = 1 << (N - 1)
    lo, hi = A, (1 << N)
    span = hi - lo
    draws = min(NULL_DRAWS, span)
    # sample distinct-ish uniform d in band (exact ints)
    nulls = [features(lo + random.randrange(span), N) for _ in range(draws)]
    for f in feat_num:
        rv = rf[f]
        lt = sum(1 for nb in nulls if nb[f] < rv)
        eq = sum(1 for nb in nulls if nb[f] == rv)
        mid = Fraction(2 * lt + eq, 2 * len(nulls))   # exact mid-rank in [0,1]
        ranks[f].append(mid)
    if rf["small_ord"] is not None:
        ord_small_real.append(rf["small_ord"])

# ---------- report ----------
def frac3(fr):
    """Fraction -> 3-decimal string via integer math only (no float)."""
    fr = Fraction(fr)
    scaled = (fr.numerator * 1000) // fr.denominator
    return f"{scaled // 1000}.{scaled % 1000:03d}"

def summarize(name, rlist):
    m = len(rlist)
    if m == 0:
        print(f"  {name:12s}: n/a"); return
    mean = sum(rlist) * Fraction(1, m)          # exact Fraction
    hi = sum(1 for r in rlist if r > Fraction(1, 2))
    lo = sum(1 for r in rlist if r < Fraction(1, 2))
    print(f"  {name:12s}: mean-rank={frac3(mean)}  (>0.5:{hi} <0.5:{lo} of {m})")

print("\nUniform-rank of real keys within matched-Farey null "
      "(0.5 = no bias; <0.5 real is LOW, >0.5 real is HIGH):")
for f in feat_num:
    summarize(f, ranks[f])

# order-of-k among coprime-n keys
if ord_small_real:
    s = sum(ord_small_real)
    print(f"\nk multiplicative order (coprime-n keys, m={len(ord_small_real)}): "
          f"ord(k)<=2 in {s}/{len(ord_small_real)} = {frac3(Fraction(s,len(ord_small_real)))}")

# raw n multiset (real)
from collections import Counter
cnt = Counter(n_list_real)
print("\nreal-key n multiset (top 15):",
      ", ".join(f"{n}:{c}" for n, c in cnt.most_common(15)))
print("squarefree-n fraction (real):",
      f"{sum(1 for n in n_list_real if mobius(n)!=0)}/{len(n_list_real)}")
