"""No exact slot-sharer, no lonely own-AP instant: what does the subject's reading set look like?
Readings s_l = d_l/m (own frame), common denominator q.  At own-AP instants n (odd) runner l sits at n*s_l (mod 8).
  finer_sharer   some l and some L | q, L >= 2, with L*s_l an integer multiple of 8
  exact_some     some l that lands exactly on the subject (n*s_l in 8Z) at some odd n: 8q/gcd(q s_l, 8q) is odd
  L_star         least lattice L (instants u = p/(8L), p odd) on the own d_min at which the subject is lonely
  pairs16        q = 2 only: the odd values of 2*s_l take all four pairs {+-1},{+-3},{+-5},{+-7} mod 16 (by inverse)"""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
def rnd(x): return floor(x + F(1, 2))
def dist8(x): y = x - 8 * floor(x / 8); return min(y, 8 - y)
def cd(x): x = x - floor(x); return min(x, 1 - x)
def lcm(a, b): return a * b // gcd(a, b)
def job(V):
    out = []
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        S = [d / m for d in ds]; A = [rnd(s) for s in S]
        if any(s.denominator == 1 and s.numerator % 8 == 0 for s in S): continue
        q = reduce(lcm, [s.denominator for s in S])
        if any(all(dist8(n * s) >= 1 for s in S) for n in range(1, 8 * q + 1, 2)): continue
        finer = any((L * s).denominator == 1 and (L * s).numerator % 8 == 0 for s in S for L in range(2, q + 1) if q % L == 0)
        exact_some = any((8 * q // gcd(int(q * s), 8 * q)) % 2 == 1 for s in S)
        Ls = None
        for L in range(1, 40):
            if any(all(cd(s * F(p, 8 * L)) >= F(1, 8) for s in S) for p in range(1, 8 * L * q + 1, 2)): Ls = L; break
        pairs = None
        if q == 2:
            odd = [int(2 * s) % 16 for s in S if int(2 * s) % 2 == 1]
            cls = {min(pow(c, -1, 16), (-pow(c, -1, 16)) % 16) for c in odd}
            pairs = cls == {1, 3, 5, 7}
        out.append(dict(q=q, finer=finer, exact_some=exact_some, L=Ls, pairs=pairs))
    return out
if __name__ == "__main__":
    rng = random.Random(30); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    arrs = []
    for qq in (2, 3, 4, 5, 6, 8, 10, 12, 16, 25):
        n = 0
        while n < 600:
            V = ok([AP[j] + F(rng.randint(-(45 * qq) // 100, (45 * qq) // 100), qq) for j in range(8)])
            if V: arrs.append(V); n += 1
    with Pool(8) as p: R = [x for r in p.map(job, arrs, chunksize=16) for x in r]
    print(f"no exact sharer, no lonely own-AP instant: {len(R)} runners")
    print("  reading denominator q:", dict(sorted(Counter(x['q'] for x in R).items())))
    print("  a finer-scale sharer (L | q, L*s in 8Z):", dict(Counter(x['finer'] for x in R)))
    print("  some runner lands exactly on the subject at some own-AP instants:", dict(Counter(x['exact_some'] for x in R)))
    print("  least lonely lattice L on the own d_min:", dict(sorted(Counter(x['L'] for x in R).items(), key=str)))
    print("  L divides q / L shares a factor with q:", dict(Counter((x['L'] is not None and x['q'] % x['L'] == 0, x['L'] is not None and gcd(x['L'], x['q']) > 1) for x in R)))
    q2 = [x for x in R if x["q"] == 2]
    print(f"  q = 2: odd doubled readings take all four slot-pairs mod 16: {sum(1 for x in q2 if x['pairs'])} of {len(q2)}")
