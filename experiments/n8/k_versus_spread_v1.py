"""How does the smallest working opening k depend on the spread S = d_max/d_min?

bounded_k_attack_v1 refuted 'k <= K0 for an absolute constant K0': a hill-climb found k = 369
on a set of spread ~14,125. So k is not absolutely bounded. But a bound in terms of the
SPREAD would still give ExistenceAt8, because f(S) is finite for every ds.

That matters because the framework already works in bounded-ratio terms -- section 8.2's
certificate is 'sup R = 31/9 for every arrangement of ratio d_max/d_min <= 26'.

Measured: the smallest k that works at ANY flank, against S.
"""
import random, math
from fractions import Fraction as F

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def min_k_any_flank(ds, KMAX=20000):
    for k in range(KMAX + 1):
        for e in ds:
            t = (F(k) + F(1, 8)) / e
            if all(circd(d * t) >= F(1, 8) for d in ds):
                return k
    return None

rng = random.Random(20260917)
buckets = {}
worst = {}
for _ in range(6000):
    lo = rng.choice([1, 1, 1, 2, 5])
    hi = rng.choice([8, 30, 100, 400, 2000, 20000, 200000])
    s = {F(rng.randint(lo * 1000, hi * 1000), 1000) for _ in range(7)}
    if len(s) != 7: continue
    ds = sorted(s)
    S = float(max(ds) / min(ds))
    k = min_k_any_flank(ds)
    if k is None: continue
    b = 0 if S < 8 else int(math.floor(math.log(S, 8)))
    buckets.setdefault(b, []).append(k)
    if k > worst.get(b, (-1, None))[0]:
        worst[b] = (k, S)

print(f"{'spread S':>18} {'sets':>6} {'median k':>9} {'90th':>6} {'max k':>7} {'max k / S':>10}")
for b in sorted(buckets):
    ks = sorted(buckets[b]); n = len(ks)
    mk, S = worst[b]
    lo8, hi8 = 8**b, 8**(b+1)
    print(f"  8^{b} .. 8^{b+1} ({lo8:>6}-{hi8:<7}) {n:>6} {ks[n//2]:>9} {ks[int(.9*n)]:>6} "
          f"{ks[-1]:>7} {mk/S:>10.3f}")
print()
allk = [k for v in buckets.values() for k in v]
print(f"total sets: {len(allk)}   overall max k: {max(allk)}")
print()
print("READING: if max k grows like S, the ratio in the last column stays roughly constant;")
print("if it grows like log S, the column falls steeply. Either way a bound k <= f(S) is")
print("enough for ExistenceAt8, since f(S) is finite for every difference set.")

print()
print("LIMIT OF THIS TABLE, and it is the important one.")
print("  These are RANDOM sets. Random sampling gives max k = 14 even at spread 4096-32768,")
print("  but the hill-climb in bounded_k_attack_v1 found k = 369 at spread ~14,125 -- 26x")
print("  worse at comparable spread. So the hard sets are RARE and random sampling does not")
print("  reach them. This table is evidence about typical behaviour and says almost nothing")
print("  about the worst case, which is what a theorem needs.")
print()
print("  Reporting the falling last column as 'k grows like log S' would therefore be exactly")
print("  the error this session has made repeatedly: taking the reach of a search for the")
print("  shape of the thing. The growth rate of the WORST case is not measured here.")
