# The residue criterion, derived and checked against the real-valued definition.
#
#   flankOpening n b k = (k + 1/n)/b = (n k + 1)/(n b).
#   Runner a is lonely at it iff circDist( a (n k + 1) / (n b) ) >= 1/n.
#   Write m = n k + 1.  a m /(n b) is at distance >= 1/n from Z iff its residue
#   x = a m mod (n b) satisfies  b <= x <= (n-1) b.
#
# So:  Lonely  iff  for all a in ds,  (a*(n*k+1)) mod (n*b)  in  [b, (n-1)*b].
import random
from fractions import Fraction as F
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def real_lonely(ds, b, k):
    t = (F(k) + F(1,n)) / F(b)
    return all(circ(F(a)*t) >= F(1,n) for a in ds)
def res_lonely(ds, b, k):
    m = n*k + 1
    return all(b <= (a*m) % (n*b) <= (n-1)*b for a in ds)
rng = random.Random(11); bad = 0; tot = 0; agree_true = 0
for _ in range(60000):
    ds = sorted(rng.sample(range(1,60), 7))
    b = rng.choice(ds); k = rng.randrange(0, 3*b+2)
    r1, r2 = real_lonely(ds,b,k), res_lonely(ds,b,k)
    tot += 1
    if r1 != r2: bad += 1
    if r1: agree_true += 1
print(f"[1] residue criterion vs real circDist : {tot} cases, disagreements {bad}, lonely in {agree_true}")

# Full finite search: (exists s>0, Lonely) iff (exists b in ds, exists k<b, residue condition).
# Check against an unbounded real search over many openings of every flank.
def finite_search(ds):
    return any(res_lonely(ds,b,k) for b in ds for k in range(b))
def wide_search(ds, span=6):
    return any(real_lonely(ds,b,k) for b in ds for k in range(span*max(ds)+3))
bad2 = 0; tot2 = 0; pos = 0
rng = random.Random(12)
for _ in range(4000):
    ds = sorted(rng.sample(range(1,26), 7))
    a, bq = finite_search(ds), wide_search(ds)
    tot2 += 1
    if a != bq: bad2 += 1
    if a: pos += 1
print(f"[2] finite residue search vs wide real search : {tot2} sets, disagreements {bad2}, lonely {pos} ({pos/tot2:.3f})")

# Does the finite search ever FAIL on an integer difference set?  That is LRC at n=8.
rng = random.Random(13); fails = []
N = 0
for _ in range(200000):
    ds = sorted(rng.sample(range(1,120), 7))
    N += 1
    if not finite_search(ds): fails.append(ds)
print(f"[3] integer difference sets tested {N}, sets with NO lonely opening: {len(fails)}")
if fails: print("    examples:", fails[:5])
